package stack;

import kotlinx.atomicfu.AtomicInt;
import kotlinx.atomicfu.AtomicRef;
import kotlinx.atomicfu.AtomicIntArray;

import java.util.concurrent.ThreadLocalRandom;

public class StackImpl implements Stack {
    private static class Node {
        final Node next;
        final int x;

        Node(final int x, final Node next) {
            this.next = next;
            this.x = x;
        }
    }

    // constants
    private static final int CAPACITY = 2;
    private static final int RETRY_COUNT = 2;
    private static final int POP_FULL_RETRY_COUNT = 1;
    private static final int SPIN_COUNT = 30;

    private static final int RESERVED_EMPTY = Integer.MIN_VALUE;
    private static final int RESERVED_DONE = RESERVED_EMPTY + 1;

    // head pointer
    private final AtomicRef<Node> head = new AtomicRef<>(null);

    private int getRandom() {
        return ThreadLocalRandom.current().nextInt(CAPACITY);
    }

    private static AtomicIntArray generateArr(final int count, final int val) {
        final AtomicIntArray ret = new AtomicIntArray(count);
        for (int i = 0; i < count; i++) {
            ret.get(i).setValue(val);
        }
        return ret;
    }

    private final AtomicIntArray elimination = generateArr(CAPACITY, RESERVED_EMPTY);

    private void pushStack(final int x) {
        while (true) {
            final Node curHead = head.getValue();
            if (head.compareAndSet(curHead, new Node(x, curHead))) {
                break;
            }
        }
    }

    private boolean pushElim(final int x) {
        if (x <= RESERVED_DONE) {
            return false;
        }
        final int random = getRandom();
        AtomicInt selected = null;
        for (int i = 0; i < RETRY_COUNT; i++) {
            final int ind = (random + i) % CAPACITY;
            final AtomicInt cur = elimination.get(ind);
            if (cur.compareAndSet(RESERVED_EMPTY, x)) {
                selected = cur;
                break;
            }
        }
        if (selected == null) {
            return false;
        }

        for (int i = 0; i < SPIN_COUNT; i++) {
            if (selected.compareAndSet(RESERVED_DONE, RESERVED_EMPTY)) {
                return true;
            }
        }
        if (selected.compareAndSet(x, RESERVED_EMPTY)) {
            return false;
        }
        final boolean test = selected.compareAndSet(RESERVED_DONE, RESERVED_EMPTY);
        assert test;
        return true;
    }

    private int popStack() {
        while (true) {
            final Node curHead = head.getValue();
            if (curHead == null) return Integer.MIN_VALUE;
            if (head.compareAndSet(curHead, curHead.next)) {
                return curHead.x;
            }
        }
    }

    private int popElim() {
        final int random = getRandom();
        for (int i = 0; i < RETRY_COUNT; i++) {
            final int ind = (random + i) % CAPACITY;
            final AtomicInt cur = elimination.get(ind);
            final int got = cur.getValue();
            if (got <= RESERVED_DONE) {
                continue;
            }
            if (cur.compareAndSet(got, RESERVED_DONE)) {
                return got;
            }
        }
        return RESERVED_EMPTY;
    }

    @Override
    public void push(final int x) {
        if (!pushElim(x)) {
            pushStack(x);
        }
    }

    @Override
    public int pop() {
        for (int i = 0; i < POP_FULL_RETRY_COUNT; i++) {
            final int got = popElim();
            if (got != RESERVED_EMPTY) {
                return got;
            }
        }
        return popStack();
    }
}
