import abc
from z3 import *
from itertools import pairwise
import os
from traceback import print_exc
from solver_test import SAT_to_Array_tests
from typing import Set

class EqTheorySolver(abc.ABC):
    @abc.abstractmethod
    def add_equal(self, a, b):
        raise NotImplementedError()

    @abc.abstractmethod
    def add_distinct(self, a, b):
        raise NotImplementedError()

    def add_literal(self, literal):
        negated = False
        while is_not(literal):
            negated = not negated
            literal = literal.arg(0)
        is_e = is_eq(literal)
        is_d = is_distinct(literal)
        if (is_d if negated else is_e):
            self.add_equal(literal.arg(0), literal.arg(1))
        elif (is_e if negated else is_d):
            self.add_distinct(literal.arg(0), literal.arg(1))
        else:
            raise NotImplementedError(literal)

    def add(self, *formulas):
        for formula in formulas:
            self.add_literal(formula)

def MyImplies(a, b):
    return Or(b, Not(a))

class SNM:
    def __init__(self):
        self.vars = dict()

    def root(self, a):
        l = self.vars.setdefault(a, [a, 0, set()])
        if l[0].eq(a):
            return l
        rt = self.root(l[0])
        l[0] = rt[0]
        return rt

    def get(self, a):
        return self.root(a)[0]

    def conc(self, a, b):
        a = self.root(a)
        b = self.root(b)
        if a[1] > b[1]:
            b[0] = a[0]
            a[1] += 1
            a[2].update(b[2])
        else:
            a[0] = b[0]
            b[1] += 1
            b[2].update(a[2])

class CongruenceSolver(EqTheorySolver):
    """
    Реализуйте решатель для бескванторного фрагмента теории неинтерпретированных функций (QF_UF)
    """
    def __init__(self):
        self.s = DPLL_T_Solver(SolverFor("QF_FD"), TheorySolver)
        self.fns = {}
        self.opts = 0
        self.calls = 0
        self.snm = SNM()

    def add(self, *formulas):
        for formula in formulas:
            if is_and(formula):
                super().add(*formula.children())
            else:
                super().add(formula)

    def trivialize(self, a, knownVar=None):
        if is_const(a):
            return a
        if is_app(a) and isinstance(a.decl(), FuncDeclRef):
            if a.num_args() == 0:
                return a
            func = a.decl()
            uses = self.fns.setdefault(func, [])
            args = tuple(map(lambda i: self.trivialize(a.arg(i)), range(a.num_args())))
            for x in uses:
                eq = True
                for i in range(len(args)):
                    if not args[i].eq(x[0][i]):
                        eq = False
                        break
                if eq:
                    self.opts += 1
                    return x[1]
            var = knownVar if knownVar is not None else FreshConst(func.range(), f'call_{func.name()}')
            self.calls += 1
            res = func(*args)
            uses.append((args, var))
            #print(f'save {var} = {func.name()}{args}')
            return var
        assert False

    def add_equal(self, a, b):
        #print(f'{a} == {b}')
        if is_const(a):
            a, b = b, a
        a = self.trivialize(a, b)
        b = self.trivialize(b)
        if is_const(a) and is_const(b):
            self.snm.conc(a, b)
        self.s.add(a == b)

    def add_distinct(self, a, b):
        #print(f'{a} != {b}')
        a = self.trivialize(a)
        b = self.trivialize(b)
        if is_const(a) and is_const(b):
            self.snm.root(a)[2].add(b)
            self.snm.root(b)[2].add(a)
        self.s.add(a != b)

    def check(self):
        was = True
        while was:
            was = False
            for fn_apps in self.fns.values():
                for app_x_i, app_x in enumerate(fn_apps):
                    for app_y_i in range(app_x_i + 1, len(fn_apps)):
                        app_y = fn_apps[app_y_i]
                        if self.snm.get(app_x[1]).eq(self.snm.get(app_y[1])):
                            continue
                        eq = True
                        for x, y in zip(app_x[0], app_y[0]):
                            if not self.snm.get(x).eq(self.snm.get(y)):
                                eq = False
                                break
                        if eq:
                            was = True
                            self.snm.conc(app_x[1], app_y[1])

        for var_name in self.snm.vars.keys():
            other = self.snm.root(var_name)
            var1 = other[0]
            for var2_ in other[2]:
                var2 = self.snm.get(var2_)
                if var1.eq(var2):
                    return unsat

        print(f'opts = {self.opts} calls = {self.calls}')
        eqs = 0
        neqs = 0
        neqs2 = 0
        for fn_apps in self.fns.values():
            for app_x_i, app_x in enumerate(fn_apps):
                for app_y_i in range(app_x_i + 1, len(fn_apps)):
                    app_y = fn_apps[app_y_i]
                    if app_x is app_y:
                        continue
                    app_x_root = self.snm.root(app_x[1])
                    app_x_klass = app_x_root[0]
                    app_y_root = self.snm.root(app_y[1])
                    app_y_klass = app_y_root[0]
                    if app_x_klass.eq(app_y_klass):
                        eqs += 1
                        continue
                    if app_x_klass in app_y_root[2]:
                        neqs2 += 1
                        self.s.add(Not(And(*[x == y for x, y in zip(app_x[0], app_y[0])])))
                        continue
                    fast = False
                    for x, y in zip(app_x[0], app_y[0]):
                        if self.snm.get(x) in self.snm.root(y)[2]:
                            fast = True
                            break
                    if fast:
                        neqs += 1
                        continue
                    self.s.add(MyImplies(And(*[x == y for x, y in zip(app_x[0], app_y[0])]), app_x[1] == app_y[1]))
        print(f"optimized out {eqs} {neqs} {neqs2}")
        res = self.s.check()
        print(res)
        return res


def CongruenceSolver_test1():
    S = DeclareSort('S')
    f = Function('f', S, S)
    x = Const('x', S)
    solver = CongruenceSolver()
    solver.add(f(f(x)) == x, f(f(f(x))) == x)
    assert solver.check() == sat
    solver.add(f(x) != x)
    assert solver.check() == unsat


def CongruenceSolver_test2():
    S = DeclareSort('S')
    a, b, c, d, e, s, t = Consts('a b c d e s t', S)
    f = Function('f', S, S, S)
    g = Function('g', S, S)
    solver = CongruenceSolver()
    solver.add(a == b, b == c, d == e, b == s, d == t, f(a, g(d)) != f(g(e), b))
    assert solver.check() == sat


def linearize(fs):
    for f in fs:
        if is_and(f):
            yield from linearize(f.children())
        elif is_or(f):
            yield from linearize([f.arg(0)])
        else:
            yield f


class ArraySolver(EqTheorySolver):
    """
    Реализуйте решатель для бескванторного фрагмента теории массивов с экстенсиональностью (QF_AX)
    """
    def __init__(self):
        #self.s = CongruenceSolver()
        self.s = SolverFor("QF_UF")
        self.arrs = {}
        self.eq_arrs = []
        self.idxs = []
        self.ors = []

    def get_arr(self, a):
        if is_const(a):
            fn = self.arrs.setdefault(a, FreshFunction(a.domain(), a.range()))
            return [a, [fn]]
        if is_store(a):
            idx = self.trivialize(a.arg(1))
            self.idxs.append(idx)
            val = self.trivialize(a.arg(2))
            arr = self.get_arr(a.arg(0))
            arr[1].append((idx, val))
            return arr
        assert False

    def trivialize(self, a):
        if is_const(a):
            return a
        if is_select(a):
            arr = self.get_arr(a.arg(0))
            idx = self.trivialize(a.arg(1))
            return self.get_by_index(arr, idx)
        assert False

    def get_by_index_impl(self, arr, idx, i, res):
        if i == 0:
            return [[res == arr[1][0](idx)]]
        others = self.get_by_index_impl(arr, idx, i - 1, res)
        for x in others:
            x.append(idx != arr[1][i][0])

        others.append([idx == arr[1][i][0], res == arr[1][i][1]])
        return others

    def get_by_index(self, arr, idx):
        self.idxs.append(idx)
        res = FreshConst(arr[0].range())
        others = self.get_by_index_impl(arr, idx, len(arr[1]) - 1, res)
        ors = [And(*x) for x in others]
        if len(ors) == 1:
            self.s.add(ors[0])
        else:
            #self.s.s.add(Or(*ors)) # for custom congruence
            self.s.add(Or(*ors))
        return res


    def add_equal(self, a, b):
        #print(f'{a} == {b}')
        if is_array_sort(a):
            a = self.get_arr(a)
            b = self.get_arr(b)
            self.eq_arrs.append((a, b))
            return
        a = self.trivialize(a)
        b = self.trivialize(b)
        self.s.add(a == b)

    def add_distinct(self, a, b):
        #print(f'{a} != {b}')
        if is_array_sort(a):
            a = self.get_arr(a)
            b = self.get_arr(b)
            idx = FreshConst(a[0].domain())
            self.s.add(self.get_by_index(a, idx) != self.get_by_index(b, idx))
            return
        a = self.trivialize(a)
        b = self.trivialize(b)
        self.s.add(a != b)

    def check(self):
        if len(self.eq_arrs) > 0:
            idxs = list(self.idxs)
            for a, b in self.eq_arrs:
                for idx in idxs:
                    self.s.add(self.get_by_index(a, idx) == self.get_by_index(b, idx))
        res = self.s.check()
        #print(res)
        return res


def ArraySolver_tests():
    Solver_test_files(ArraySolver, linearize, "QF_AX")


def Solver_test_file(SolverConstr, preprocess, filename):
    print(filename)
    fs = list(preprocess(parse_smt2_file(filename)))
    solver = SolverConstr()
    gold_solver = Solver()
    gold_solver.add(*fs)
    desired_result = gold_solver.check()
    solver.add(*fs)
    assert solver.check() == desired_result


def Solver_test_files(SolverConstr, preprocess, benchmark_dir):
    for base, _, filenames in os.walk(benchmark_dir):
        for filename in filenames:
            Solver_test_file(SolverConstr, preprocess, os.path.join(base, filename))


def CongruenceSolver_tests():
    CongruenceSolver_test1()
    CongruenceSolver_test2()
    Solver_test_files(CongruenceSolver, linearize, "QF_UF")


class DPLL_T_Solver:
    """
    Реализуйте DPLL(T) решатель. Вы можете только:
    - использовать готовый решатель self.prop_solver
    - создавать решатели теорий при помощи конструктора решателей self.theories_solver
    Другие решатели создавать и использовать запрещено.
    """
    def __init__(self, prop_solver, theory_solver):
        self.prop_solver = prop_solver
        self.theories_solver = theory_solver
        self.hh = theory_solver()
        self.ors = []

    def add(self, *fs):
        for x in fs:
            if is_and(x):
                for y in range(x.num_args()):
                    self.add(x.arg(y))
            elif is_or(x):
                if x.num_args() == 1:
                    self.hh.add(x.arg(0))
                    return
                b = FreshBool()
                self.ors.append((b, [x.arg(i) for i in range(x.num_args())]))
                self.hh.add(b)
            else:
                self.hh.add(*fs)

    def check(self):
        print('ors', len(self.ors))
        def traverse(accum, entire, partial, i=0):
            # print('traverse', i, 'of', len(self.ors))
            if i >= len(self.ors):
                return entire(accum)
            check = []
            idx = 0
            for t in self.ors[i][1]:
                idx += 1
                cp = accum[:i]
                cp.append((self.ors[i][0], t))
                if partial(cp):
                    check.append((self.ors[i][0], t))
                #else:
                #    print(f'fast fail {idx}/{len(self.ors[i][1])}')
            for t in check:
                accum[i] = t
                ls = traverse(accum, entire, partial, i + 1)
                if ls != None:
                    return ls

        def entire(name_term_list):
            self.hh.push()
            for var, term in name_term_list:
                self.hh.add(var == term)
            res = self.hh.check()
            assert res != unknown
            self.hh.pop()
            if res == sat:
                print("done")
                return sat
        def partial(name_term_list):
            self.hh.push()
            for var, term in name_term_list:
                self.hh.add(var == term)
            res = self.hh.check()
            assert res != unknown
            self.hh.pop()
            return res == sat

        res = self.hh.check()
        if res == unsat:
            return unsat
        # lastChecked = [x[0] != self.hh.model()[x[0]] for x in self.ors]
        res = traverse([None] * len(self.ors), entire, partial)
        if res is not None:
            return res
        return unsat

        #while len(self.ors) != 0:
        #    last = self.ors.pop()
        #    print(last)
        #    ok = False
        #    for term in last[1]:
        #        self.hh.push()
        #        self.add(last[0] == term)
        #        st = self.hh.check()
        #        self.hh.pop()
        #        assert st != unknown
        #        if st == sat:
        #            ok = True
        #            self.add(last[0] == term)
        #            break
        #    if not ok:
        #        print('unsat')
        #        return unsat
        #print('sat')
        #return sat


def DPLL_T_Solver_test1(theory_solver):
    Z = IntSort()
    f = Function('f', Z, Z)
    x, y, z = Ints('x y z')
    A = Array('A', Z, Z)
    s = DPLL_T_Solver(SolverFor("QF_FD"), theory_solver)
    s.add(x + 2 == y)
    s.add(f(Store(A, x, 3)[y - 2]) != f(y - x + 1))
    assert s.check() == unsat


def DPLL_T_Solver_tests_general(theory_solver):
    DPLL_T_Solver_test1(theory_solver)
    Solver_test_files(lambda: DPLL_T_Solver(SolverFor("QF_FD"), theory_solver), list, "QF_AUFLIA")


class TheorySolver:
    def __init__(self):
        self.solver = Solver()
        self.solver.set(unsat_core=True)
        self.ps = dict()

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def add(self, *args):
        for arg in args:
            assert not (is_and(arg) or is_or(arg)), f"Theory solver obtained {arg}, which is not a literal"
        for arg in args:
            p = FreshBool()
            self.solver.assert_and_track(arg, p)
            self.ps[p] = arg

    def check(self):
        return self.solver.check()

    def model(self):
        return self.solver.model()

    def unsat_core(self):
        core = self.solver.unsat_core()
        return [self.ps[v] for v in core]


def DPLL_T_Solver_tests():
    DPLL_T_Solver_tests_general(TheorySolver)


def maxsat(s: Solver, Fs: Set[BoolRef]):
    """
    Реализуйте MaxSat решатель
    :param s: Solver, such that `s.check() == sat`
    :param Fs: a set of formulas
    :return: maximum subset `Ms` of `Fs` such that `s.check(Ms) == sat`
    """
    assert s.check() == sat
    fs = list(Fs)

    s.push()

    rs = Bools(' '.join([f'relaxed{i}' for i in range(len(fs))]))
    fs_relaxed = [Or(x, y) for x, y in zip(fs, rs)]
    best = []
    for f in fs_relaxed:
        s.add(f)
    better = sum([If(r, 0, 1) for r in rs])
    upper = len(fs) + 1
    while True:
        s.push()
        m = (len(best) + upper) // 2
        #print(f'lo={len(best)} hi={upper} m={m}')
        s.add(better > m)
        s.add(better <= upper)
        res = s.check()
        #print(res)
        if res == sat:
            best = [fs[i] for i, r in enumerate(rs) if s.model()[r] == False]
            #print(f'best={len(best)}')
            s.pop()
        elif res == unsat:
            s.pop()
            if upper > len(best):
                upper = m
                continue
            s.pop()
            return set(best)
        else:
            assert False

def maxsat_test():
    a, b, c = Bools('a b c')
    o = Solver()
    o.add(a == c)
    o.add(Not(And(a, b)))
    assert maxsat(o, {a, b, c}) == {a, c}


def dimacs2z3(clause):
    def lit2z3(lit):
        v = Bool(str(abs(lit)))
        if lit < 0:
            return Not(v)
        return v
    return Or([lit2z3(lit) for lit in clause])


def parse_wcnf(line):
    line = line.strip()
    if line.startswith("c"):
        return None
    clause = [x.strip() for x in line.split(' ')]
    hard = False
    if clause[0] == 'h':
        hard, clause = True, clause[1:]
    clause = dimacs2z3([int(x) for x in clause[:-1]])
    return hard, clause


def maxsat_tests():
    maxsat_test()
    for entry in os.scandir("WCNF"):
        print(entry.path)
        s = Solver()
        o = Optimize()
        soft = set()
        with open(os.path.join(entry.path)) as file:
            for line in file:
                hardAndClause = parse_wcnf(line)
                if hardAndClause is None:
                    continue
                hard, clause = hardAndClause
                if hard:
                    s.add(clause)
                    o.add(clause)
                else:
                    soft.add(clause)
                    o.add_soft(clause)
        o.check()
        m = o.model()
        assert maxsat(s, soft) == {x for x in soft if is_true(m.eval(x))}


def check_unsat(fs):
    solver = Solver()
    solver.add(fs)
    return solver.check() == unsat

class MyExc(Exception):
    pass

def check_follows(fromF, toF):
    return check_unsat(And(fromF, mk_not(toF)))

def mk_lit(m, x):
    return x if is_true(m.eval(x)) else mk_not(x)
def interpolate(phi, psi, xs):
    """
    :param phi и psi: формулы *только* над булевыми переменными, такие, что (phi /\ psi) unsat
    :param xs: общие переменные phi и psi
    :return булева формула i над переменными xs, такая что: phi |= i и (psi /\ i) unsat
    Замечание: можно создавать только решатели `SolverFor("QF_FD")` и никаких других
    Замечание: множество всех моделей phi является корректным интерполянтом, однако на практике такой интерполянт будет очень большим - реализуйте такую интерполяцию
    Замечание: попробуйте изменить код для идеи выше так, строя меньший интерполянт из unsat ядер
    """
    assert check_unsat(And(phi, psi))

    xs_set = set(xs)
    def collect(a, to):
        if is_const(a):
            if a not in xs_set:
                to.add(a)
            return to
        for i in range(a.num_args()):
            collect(a.arg(i), to)
        return to
    only_phi_vars = list(collect(phi, set()))
    only_psi_vars = list(collect(psi, set()))
    all_phi_vars = only_phi_vars + xs
    all_psi_vars = only_psi_vars + xs
    all_vars = only_phi_vars + xs + only_psi_vars

    def build_clause(accum, i=0):
        if i == len(xs):
            if len(accum) > 0:
                yield accum
            return
        yield from build_clause(accum, i+1)
        accum.append(xs[i])
        yield from build_clause(accum, i+1)
        accum[-1] = Not(xs[i])
        yield from build_clause(accum, i+1)
        accum.pop()

    def make(accum, i=0):
        if i == len(accum):
            yield accum
            return
        accum[i] = False
        yield from make(accum, i+1)
        accum[i] = True
        yield from make(accum, i+1)

    def eval_clause(exp, dic):
        if is_const(exp):
            return dic[exp]
        lst = [eval_clause(exp.arg(i), dic) for i in range(exp.num_args())]
        if is_and(exp):
            return all(lst)
        if is_not(exp):
            return not lst[0]
        if is_implies(exp):
            return not lst[0] or lst[1]
        if is_or(exp):
            return any(lst)
        if is_eq(exp):
            return lst[0] == lst[1]
        if is_distinct(exp):
            return lst[0] != lst[1]
        print(exp)
        assert False

    clauses_cnt = 0
    while True:
        clauses_cnt += 1
        assert clauses_cnt < 3
        #print('try ', clauses_cnt)
        def tryy(i, ands):
            if i == clauses_cnt:
                formula = And(*ands)
                ok = True
                for all_vars_vals in make([None for i in range(len(all_vars))]):
                    dic = dict(zip(all_vars, all_vars_vals))
                    if not eval_clause(Implies(phi, formula), dic):
                        ok = False
                        break
                    if not eval_clause(Not(And(psi, formula)), dic):
                        ok = False
                        break

                #s.add(ForAll(all_phi_vars, Implies(phi, formula)))
                #s.add(ForAll(all_psi_vars, Not(And(psi, formula))))
                #chk = s.check()
                #print(clauses_cnt, i, formula, chk, len(ands))
                #if chk == sat:
                if ok:
                    ex = MyExc()
                    ex.formula = formula
                    raise ex
                return
            ands.append(None)
            for attempt in build_clause([]):
                ands[-1] = Or(*attempt)
                tryy(i + 1, ands)
            ands.pop()
        try:
            tryy(0, [])
        except MyExc as e:
            #print('found', e.formula)
            return e.formula


def interpolate_test_general(phi, psi, xs):
    i = interpolate(phi, psi, xs)
    assert check_follows(And(phi), i)
    assert check_unsat(And(i, psi))


def interpolate_test1():
    a1, a2, b1, b2, x1, x2 = Bools('a1 a2 b1 b2 x1 x2')
    phi = And(a1 == x1, a2 != a1, a2 != x2)
    psi = And(b1 == x1, b2 != b1, b2 == x2)
    #x1=t x2=f
    #a1=t a2!=f a2!=t
    interpolate_test_general(phi, psi, [x1, x2])


def interpolate_test2():
    x0, x1, x2 = Bools('x0 x1 x2')
    phi = And(Not(x0), Or(x0, x2), Or(Not(x1), Not(x2)))
    psi = And(Not(x2), Or(x1, x2))
    interpolate_test_general(phi, psi, [x1, x2])


def interpolate_test3():
    x, y1, y2, z = Bools('x y1 y2 z')
    phi = And(Or(x, Not(y1)), Or(Not(x), Not(y2)), y1)
    psi = And(Or(Not(y1), y2), Or(y1, z), Not(z))
    interpolate_test_general(phi, psi, [y1, y2])


def interpolate_test4():
    r, p, q = Bools('r p q')
    phi = And(Not(r), Or(r, p))
    psi = And(q, Or(Not(p), Not(q)))
    interpolate_test_general(phi, psi, [p])


def interpolate_test5():
    a1, a2, a3, a4 = Bools('a1 a2 a3 a4')
    phi = And(Or(a1, Not(a2)), Or(Not(a1), Not(a3)))
    psi = And(Or(Not(a2), a3), Or(a2, a4), Not(a4))
    interpolate_test_general(phi, psi, [a2, a3])


def interpolate_tests():
    interpolate_test1()
    interpolate_test2()
    interpolate_test3()
    interpolate_test4()
    interpolate_test5()


def lia_elim():
    """
    Напишите в `psi` формулу без кванторов, эквивалентную формуле `phi`
    """
    x, y, z = Ints("x y z")
    phi = ForAll(x, Implies(y > 2 * x + 2, 3 * x != z))

    # !exists x, !(y > 2x + 2 => 3x != z)
    l1 = y
    l2 = 2*x + 2
    r1 = 3*x
    r2 = z
    # !exists x, !((r1 != r2) \/ !(l1 > l2))
    # !exists x, !((r1 != r2) \/ (l1 <= l2))
    # !exists x, (r1 == r2) /\ (l1 > l2)
    # !exists x, r1 < r2 + 1 /\ r2 < r1 + 1 /\ l2 < l1
    # !exists x, 3x < z + 1 /\ z < 3x + 1 /\ 2x + 2 < y
    # !exists x, 3x < z + 1 /\ z - 1 < 3x /\ 2x < y - 2
    # !exists x, 6x < 2z + 2 /\ 2z - 2 < 6x /\ 6x < 3y - 6
    # !exists q, q < 2z + 2 /\ 2z - 2 < q /\ q < 3y - 6 /\ q % 6 == 0
    delta = 6
    ors = []
    for b in [2*z - 2]:
        for j in range(1, delta + 1):
            q = b + j
            ors.append(And(q < 2*z + 2, 2*z - 2 < q, q < 3*y - 6, q % 6 == 0))

    psi = Not(Or(*ors))
    # psi = Not(Exists(x, And(x < 2*z + 2, 2*z - 2 < x, x < 3*y - 6, x % 6 == 0)))

    s = Solver()
    s.add(phi != psi)
    assert s.check() == unsat


def main():
    total_points = 0
    tests = {
        CongruenceSolver_tests: 20,
        ArraySolver_tests: 10,
        DPLL_T_Solver_tests: 5,
        SAT_to_Array_tests: 5,
        maxsat_tests: 5,
        interpolate_tests: 4,
        lia_elim: 1,
    }
    for test, points in tests.items():
        try:
            print(f'running {test.__name__}')
            test()
            print(f"Gained +{points} for {test.__name__}")
            total_points += points
        except Exception:
            print(f"Gained no points for {test.__name__} because of error:")
            print_exc(None, sys.stdout, False)
    print(f"Total points for this homework: {total_points}")


if __name__ == "__main__":
    main()
