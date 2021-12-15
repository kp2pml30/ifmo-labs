#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"
#include "proc.h"
#include "defs.h"

#define DEBUG_OUTPUT(a) // printf("%s -- %d %d\n", a, cpuid(), __LINE__);

#ifndef offsetof
#define offsetof(a,b) ((uint64)(&(((a*)(0))->b)))
#endif

struct cpu cpus[NCPU];

struct proc *initproc;

int nextpid = 1;
struct spinlock pid_lock;

extern void forkret(void);
static void wakeup1(struct proc *chan);

extern char trampoline[]; // trampoline.S

struct forward_lst {
  struct forward_lst *next;
};

struct proc_lst {
  struct forward_lst lst;
  struct proc proc;
};

struct {
  struct forward_lst *next;
  struct spinlock lock;
} proc_head;

// cast proc to list item
struct proc_lst *
proc_to_lst(struct proc *proc)
{
  struct proc_lst *ret = (struct proc_lst *)((char *)proc - offsetof(struct proc_lst, proc));
  return ret;
}

// for kstack allocation, better to use vector here
struct page_lst {
  struct list lst;
  uint64 stack;
};
struct list page_head;
struct spinlock page_lst_lock;
int kstack_next_index = 0;

struct spinlock proc_count_lck;
int proc_count;
int proc_count_handler(int d){
  acquire(&proc_count_lck);
  int ret = proc_count;
  proc_count += d;
  release(&proc_count_lck);
  return ret;
}


static uint64
alloc_new_kstack(void)
{
  char *pa = kalloc();
  if(pa == 0)
    panic("kalloc");
  // called only with locked
  uint64 va = KSTACK(kstack_next_index++);
  kvmmap(va, (uint64)pa, PGSIZE, PTE_R | PTE_W);
  return va;
}
static void
put_kstack_back(uint64 va)
{
  struct page_lst *ret = bd_malloc(sizeof(struct page_lst));
  if (ret == 0)
    panic("no memmory for page");
  lst_init(&ret->lst);
  ret->stack = va;
  acquire(&page_lst_lock);
  lst_push(&page_head, ret);
  release(&page_lst_lock);
}
static uint64
get_kstack(void)
{
  uint64 ret;
  acquire(&page_lst_lock);
  if (lst_empty(&page_head))
     ret = alloc_new_kstack();
  else {
    struct page_lst *pop = lst_pop(&page_head);
    ret = pop->stack;
    bd_free(pop);
  }
  release(&page_lst_lock);
  return ret;
}

void
procinit(void)
{
  proc_head.next = 0;
  initlock(&pid_lock, "nextpid");
  initlock(&page_lst_lock, "kstack list");
  initlock(&proc_head.lock, "proc head");
  lst_init(&page_head);
  kvminithart();

  initlock(&proc_count_lck, "proc count lock");
  proc_count = 0;
}

// Must be called with interrupts disabled,
// to prevent race with process being moved
// to a different CPU.
int
cpuid()
{
  int id = r_tp();
  return id;
}

// Return this CPU's cpu struct.
// Interrupts must be disabled.
struct cpu*
mycpu(void) {
  int id = cpuid();
  struct cpu *c = &cpus[id];
  return c;
}

// Return the current struct proc *, or zero if none.
struct proc*
myproc(void) {
  push_off();
  struct cpu *c = mycpu();
  struct proc *p = c->proc;
  pop_off();
  return p;
}

int
allocpid() {
  int pid;

  acquire(&pid_lock);
  pid = nextpid;
  nextpid = nextpid + 1;
  release(&pid_lock);

  return pid;
}

// does not push
static struct proc_lst *
allocproc_lst(void)
{
  struct proc_lst *ret = bd_malloc(sizeof(struct proc_lst));
  if (ret == 0)
    return 0;
  ret->lst.next = 0;
  memset(&ret->proc, 0, sizeof(struct proc));
  initlock(&ret->proc.lock, "proc");
  ret->proc.kstack = get_kstack();

  acquire(&ret->proc.lock);
  return ret;
}

// Look in the process table for an UNUSED proc.
// If found, initialize state required to run in the kernel,
// and return with p->lock held.
// If there are no free procs, return 0.
// does not push
static struct proc*
allocproc(void)
{
  struct proc_lst *p_i = allocproc_lst();
  if (p_i == 0)
    return 0;
  struct proc *p = &p_i->proc;

  p->pid = allocpid();

  // Allocate a trapframe page.
  if((p->tf = (struct trapframe *)kalloc()) == 0){
    release(&p->lock);
    put_kstack_back(p->kstack);
    bd_free(p_i);
    return 0;
  }

  // An empty user page table.
  p->pagetable = proc_pagetable(p);

  // Set up new context to start executing at forkret,
  // which returns to user space.
  memset(&p->context, 0, sizeof p->context);
  p->context.ra = (uint64)forkret;
  p->context.sp = p->kstack + PGSIZE;

  return p;
}
static void
push_proc(struct proc *p)
{
  proc_count_handler(+1);
  struct proc_lst *p_i = proc_to_lst(p);
  acquire(&proc_head.lock);
  if (proc_head.next == 0){
    proc_head.next = &p_i->lst;
    release(&proc_head.lock);
    return;
  }
  release(&proc_head.lock);
  struct proc *mproc = myproc();
  if (mproc == 0)
    panic("allocproc from no proc");
  // mproc is locked if we are executing it
  struct proc_lst *m = proc_to_lst(mproc);
  p_i->lst.next = m->lst.next;
  m->lst.next = &p_i->lst;
}

// free a proc structure and the data hanging from it,
// including user pages.
// p->lock must be held.
// p must be detatched
static void
freeproc(struct proc *p)
{
  if(p->tf)
    kfree((void*)p->tf);
  p->tf = 0;
  if(p->pagetable)
    proc_freepagetable(p->pagetable, p->sz);
  p->pagetable = 0;
  p->sz = 0;
  p->pid = 0;
  p->parent = 0;
  p->name[0] = 0;
  p->chan = 0;
  p->killed = 0;
  p->xstate = 0;
  p->state = UNUSED;
  struct proc_lst *p_i = proc_to_lst(p);
  put_kstack_back(p_i->proc.kstack);
  release(&p->lock);
  bd_free(p_i);
}

// both must be locked, will remain same
static void
detatchproc(struct forward_lst **prevlnk, struct proc_lst *next)
{
  *prevlnk = next->lst.next;
  next->lst.next = 0;
  proc_count_handler(-1);
}

static struct proc *
proc_lst_begin(void)
{
  struct proc *mproc = myproc();
  if (mproc == 0){
    acquire(&proc_head.lock);
    struct proc_lst *next = (void *)proc_head.next;
    if (next == 0){
      release(&proc_head.lock);
      return 0;
    }
    acquire(&next->proc.lock);
    release(&proc_head.lock);
    return &next->proc;
  }
  struct proc_lst *m_i = proc_to_lst(mproc);
  struct proc_lst *next = (void *)m_i->lst.next;
  if (next == 0)
    return 0;
  acquire(&next->proc.lock);
  return &next->proc;
}
static int
proc_lst_nend(struct proc *p)
{
  return p != 0;
}
static struct proc *
proc_lst_inc(struct proc *p)
{
  struct proc_lst
    *p_i = proc_to_lst(p),
    *next = (void *)p_i->lst.next;
  if (next == 0)
  {
    release(&p->lock);
    return 0;
  }
  acquire(&next->proc.lock);
  release(&p->lock);
  return &next->proc;
}

#define PROC_LST_ITERATE(name) for (name = proc_lst_begin(); proc_lst_nend(name); name = proc_lst_inc(name))

struct wait_iterator {
  struct forward_lst **link;
  struct spinlock *lock;
  struct proc_lst *cur;
};
static void
proc_lst_wbegin(struct wait_iterator *p)
{
  DEBUG_OUTPUT(">wbeg");
  struct proc *mproc = myproc();
  if (mproc == 0)
    panic("wait from no proc");
  struct proc_lst *head = proc_to_lst(mproc);
  struct proc_lst *next = (void *)head->lst.next;
  if (next == 0){
    p->link = 0;
    p->lock = 0;
    p->cur = 0;
    DEBUG_OUTPUT("<wbeg");
    return;
  }
  acquire(&next->proc.lock);
  p->link = &head->lst.next;
  p->lock = 0;
  p->cur = next;
  DEBUG_OUTPUT("<wbeg");
}
static int
proc_lst_wnend(struct wait_iterator *p)
{
  return p->cur != 0;
}
static void
proc_lst_winc(struct wait_iterator *p)
{
  DEBUG_OUTPUT(">winc");
  if (p->lock != 0)
    release(p->lock);
  struct proc_lst *next = (void *)p->cur->lst.next;
  if (next == 0)
  {
    release(&p->cur->proc.lock);
    p->cur = 0;
    DEBUG_OUTPUT("<winc end");
    return;
  }
  p->link = &p->cur->lst.next;
  p->lock = &p->cur->proc.lock;
  acquire(&next->proc.lock);
  p->cur = next;
  DEBUG_OUTPUT("<winc");
}

// Create a page table for a given process,
// with no user pages, but with trampoline pages.
pagetable_t
proc_pagetable(struct proc *p)
{
  pagetable_t pagetable;

  // An empty page table.
  pagetable = uvmcreate();

  // map the trampoline code (for system call return)
  // at the highest user virtual address.
  // only the supervisor uses it, on the way
  // to/from user space, so not PTE_U.
  mappages(pagetable, TRAMPOLINE, PGSIZE,
           (uint64)trampoline, PTE_R | PTE_X);

  // map the trapframe just below TRAMPOLINE, for trampoline.S.
  mappages(pagetable, TRAPFRAME, PGSIZE,
           (uint64)(p->tf), PTE_R | PTE_W);

  return pagetable;
}

// Free a process's page table, and free the
// physical memory it refers to.
void
proc_freepagetable(pagetable_t pagetable, uint64 sz)
{
  uvmunmap(pagetable, TRAMPOLINE, PGSIZE, 0);
  uvmunmap(pagetable, TRAPFRAME, PGSIZE, 0);
  if(sz > 0)
    uvmfree(pagetable, sz);
}

// a user program that calls exec("/init")
// od -t xC initcode
uchar initcode[] = {
  0x17, 0x05, 0x00, 0x00, 0x13, 0x05, 0x05, 0x02,
  0x97, 0x05, 0x00, 0x00, 0x93, 0x85, 0x05, 0x02,
  0x9d, 0x48, 0x73, 0x00, 0x00, 0x00, 0x89, 0x48,
  0x73, 0x00, 0x00, 0x00, 0xef, 0xf0, 0xbf, 0xff,
  0x2f, 0x69, 0x6e, 0x69, 0x74, 0x00, 0x00, 0x01,
  0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00
};

// Set up first user process.
void
userinit(void)
{
  struct proc *p;

  p = allocproc();
  initproc = p;

  // allocate one user page and copy init's instructions
  // and data into it.
  uvminit(p->pagetable, initcode, sizeof(initcode));
  p->sz = PGSIZE;

  // prepare for the very first "return" from kernel to user.
  p->tf->epc = 0;      // user program counter
  p->tf->sp = PGSIZE;  // user stack pointer

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;

  push_proc(p);

  release(&p->lock);
}

// Grow or shrink user memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *p = myproc();

  sz = p->sz;
  if(n > 0){
    if((sz = uvmalloc(p->pagetable, sz, sz + n)) == 0) {
      return -1;
    }
  } else if(n < 0){
    if((sz = uvmdealloc(p->pagetable, sz, sz + n)) == 0) {
      return -1;
    }
  }
  p->sz = sz;
  return 0;
}

// Create a new process, copying the parent.
// Sets up child kernel stack to return as if from fork() system call.
int
fork(void)
{
  if (proc_count_handler(0) > NPROC)
    return -1;

  int i, pid;
  struct proc *np;
  struct proc *p = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy user memory from parent to child.
  if(uvmcopy(p->pagetable, np->pagetable, p->sz) < 0){
    freeproc(np);
    return -1;
  }
  np->sz = p->sz;

  np->parent = p;

  // copy saved user registers.
  *(np->tf) = *(p->tf);

  // Cause fork to return 0 in the child.
  np->tf->a0 = 0;

  // increment reference counts on open file descriptors.
  for(i = 0; i < NOFILE; i++)
    if(p->ofile[i])
      np->ofile[i] = filedup(p->ofile[i]);
  np->cwd = idup(p->cwd);

  safestrcpy(np->name, p->name, sizeof(p->name));

  pid = np->pid;

  np->state = RUNNABLE;

  push_proc(np);
  release(&np->lock);

  return pid;
}

// Pass p's abandoned children to init.
// Caller must hold p->lock and p->parent->lock
// returns 1 if there were a zombie
static int
reparent(struct proc *p) {
  struct proc *pp;
  int waszomb = 0;

  DEBUG_OUTPUT(">reparent for");
  PROC_LST_ITERATE(pp){
    DEBUG_OUTPUT("-reparent for");
    if(pp->parent == p){
      pp->parent = initproc;
      if(pp->state == ZOMBIE)
        waszomb = 1;
    }
  }
  DEBUG_OUTPUT("<reparent for");
  return waszomb;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait().
void
exit(int status)
{
  struct proc *p = myproc();

  if(p == initproc)
    panic("init exiting");

  // Close all open files.
  for(int fd = 0; fd < NOFILE; fd++){
    if(p->ofile[fd]){
      struct file *f = p->ofile[fd];
      fileclose(f);
      p->ofile[fd] = 0;
    }
  }

  begin_op(ROOTDEV);
  iput(p->cwd);
  end_op(ROOTDEV);
  p->cwd = 0;

  DEBUG_OUTPUT(">acq parent");
  acquire(&p->parent->lock);
  DEBUG_OUTPUT("<acq parent");
  acquire(&p->lock);
  DEBUG_OUTPUT("<acq self");

  // Give any children to init.
  int wakeinit = reparent(p);

  // Parent might be sleeping in wait().
  wakeup1(p->parent);
  release(&p->parent->lock);

  if (wakeinit){
    DEBUG_OUTPUT(">acq init");
    acquire(&initproc->lock);
    DEBUG_OUTPUT("<acq init");
    wakeup1(initproc);
    release(&initproc->lock);
  }

  p->xstate = status;
  p->state = ZOMBIE;

  // Jump into the scheduler, never to return.
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(uint64 addr)
{
  struct proc *np;
  int havekids, pid;
  struct proc *p = myproc();

  // hold p->lock for the whole time to avoid lost
  // wakeups from a child's exit().
  acquire(&p->lock);

  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    struct wait_iterator it;
    for (proc_lst_wbegin(&it); proc_lst_wnend(&it); proc_lst_winc(&it)) {
      np = &it.cur->proc;
      if(np->parent == p){
        // np->parent can't change between the check and the acquire()
        // because only the parent changes it, and we're the parent.
        havekids = 1;
        if(np->state == ZOMBIE){
          // Found one.
          pid = np->pid;
          if(addr != 0 && copyout(p->pagetable, addr, (char *)&np->xstate,
                                  sizeof(np->xstate)) < 0) {
            panic("rjaka"); // todo
            release(&p->lock);
            return -1;
          }
          detatchproc(it.link, it.cur);
          freeproc(np);
          if (it.lock != 0)
            release(it.lock);
          release(&p->lock);
          return pid;
        }
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || p->killed){
      release(&p->lock);
      return -1;
    }

    // Wait for a child to exit.
    sleep(p, &p->lock);  //DOC: wait-sleep
  }
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run.
//  - swtch to start running that process.
//  - eventually that process transfers control
//    via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();

  c->proc = 0;
  for(;;){
    // Avoid deadlock by ensuring that devices can interrupt.
    intr_on();

    int found = 0;
    PROC_LST_ITERATE(p){
      if(p->state == RUNNABLE) {
        // Switch to chosen process.  It is the process's job
        // to release its lock and then reacquire it
        // before jumping back to us.
        p->state = RUNNING;
        c->proc = p;
        swtch(&c->scheduler, &p->context);

        // Process is done running for now.
        // It should have changed its p->state before coming back.
        c->proc = 0;

        found = 1;
      }
    }
    if(found == 0){
      intr_on();
      asm volatile("wfi");
    }
  }
}

// Switch to scheduler.  Must hold only p->lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->noff, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&p->lock))
    panic("sched p->lock");
  if(mycpu()->noff != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(intr_get())
    panic("sched interruptible");

  intena = mycpu()->intena;
  swtch(&p->context, &mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  struct proc *p = myproc();
  acquire(&p->lock);
  p->state = RUNNABLE;
  sched();
  release(&p->lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch to forkret.
void
forkret(void)
{
  static int first = 1;

  // Still holding p->lock from scheduler.
  release(&myproc()->lock);

  if (first) {
    // File system initialization must be run in the context of a
    // regular process (e.g., because it calls sleep), and thus cannot
    // be run from main().
    first = 0;
    fsinit(minor(ROOTDEV));
  }

  usertrapret();
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();

  // Must acquire p->lock in order to
  // change p->state and then call sched.
  // Once we hold p->lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup locks p->lock),
  // so it's okay to release lk.
  if(lk != &p->lock){  //DOC: sleeplock0
    acquire(&p->lock);  //DOC: sleeplock1
    release(lk);
  }

  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &p->lock){
    release(&p->lock);
    acquire(lk);
  }
}

// Wake up all processes sleeping on chan.
// Must be called without any p->lock.
void
wakeup(void *chan)
{
  struct proc *p = initproc;
  for(acquire(&p->lock); proc_lst_nend(p); p = proc_lst_inc(p)){
    if(p->state == SLEEPING && p->chan == chan) {
      p->state = RUNNABLE;
    }
  }
}

// Wake up p if it is sleeping in wait(); used by exit().
// Caller must hold p->lock.
static void
wakeup1(struct proc *p)
{
  if(p->chan == p && p->state == SLEEPING) {
    p->state = RUNNABLE;
  }
}

// Kill the process with the given pid.
// The victim won't exit until it tries to return
// to user space (see usertrap() in trap.c).
int
kill(int pid)
{
  struct proc *p = initproc;
  for(acquire(&p->lock); proc_lst_nend(p); p = proc_lst_inc(p)){
    if(p->pid == pid){
      p->killed = 1;
      if(p->state == SLEEPING){
        // Wake process from sleep().
        p->state = RUNNABLE;
      }
      release(&p->lock);
      return 0;
    }
  }
  return -1;
}

// Copy to either a user address, or kernel address,
// depending on usr_dst.
// Returns 0 on success, -1 on error.
int
either_copyout(int user_dst, uint64 dst, void *src, uint64 len)
{
  struct proc *p = myproc();
  if(user_dst){
    return copyout(p->pagetable, dst, src, len);
  } else {
    memmove((char *)dst, src, len);
    return 0;
  }
}

// Copy from either a user address, or kernel address,
// depending on usr_src.
// Returns 0 on success, -1 on error.
int
either_copyin(void *dst, int user_src, uint64 src, uint64 len)
{
  struct proc *p = myproc();
  if(user_src){
    return copyin(p->pagetable, dst, src, len);
  } else {
    memmove(dst, (char*)src, len);
    return 0;
  }
}

// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  struct proc *p;
  char *state;

  printf("\n");
  panic("procdump");
  for(p = 0; p < 0; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    printf("%d %s %s", p->pid, state, p->name);
    printf("\n");
  }
}
