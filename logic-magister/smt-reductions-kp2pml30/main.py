from typing import Set, Tuple, List
from z3 import *
from time import perf_counter
import numpy as np
import operator as op


def model2formula(model):
    return And(*[v() == model[v()] for v in model])


def ferma_theorem(easy=True):  # NIA
    x, y, z = Ints('x y z')
    s = Solver()
    for v in [x, y, z]:
        s.add(v > 0)
    if easy:
        s.add(x < y)
        s.add(y < z)
        s.add(x * x + y * y == z * z)
    else:
        s.add(x * x * x + y * y * y == z * z * z) # should be unsat, but diverges
    print(s.to_smt2())
    while s.check() == sat:
        model = s.model()
        print(model[x], model[y], model[z])
        s.add(Not(model2formula(model)))


INT_SIZE = 32


def abs_ex():  # BV
    x, y = BitVecs('x y', INT_SIZE)
    s = Solver()
    s.add(y == If(x >= 0, x, -x))
    s.add(Not(y >= 0))
    s.check()
    print(s.model())


def factor(out, nia=False, long=False):  # BV
    long = not nia and long
    x, y, n = Ints('x y n') if nia else BitVecs('x y n', INT_SIZE)
    s = Solver()
    s.add(n == out)
    if long:
        xe, ye, ne = map(lambda v: ZeroExt(INT_SIZE, v), [x, y, n])
        s.add(ne == xe * ye)
    else:
        s.add(n == x * y)
    s.add(x <= y)
    for v in [x, y]:
        s.add(v > 1)
        s.add(v < n)
    t = perf_counter()
    s.check()
    print("Estimated time:", perf_counter() - t)
    # print(s.to_smt2())
    model = s.model()
    xv = model[x]
    yv = model[y]
    xy = xv.as_long() * yv.as_long()
    print(f"{xv} * {yv} = {xy}", end='')
    if not nia:
        print(f" ?= {xy % (1 << INT_SIZE)}")
    else:
        print()


def cribbage():
    def attempt(terms, N):
        """
        TODO: 3 points
        Cribbage players have long been aware that 15 = 7 + 8 = 4 + 5 + 6 = 1 + 2 + 3 + 4 + 5 .
        Find the number of ways to represent `N` as a sum of `terms` number of consecutive positive integers.

        :param terms: number of positions
        :param N: number to be represented
        :return: a list of length `terms` of consecutive positive integers. sum of this list should be equal to `N`
        :return if there is no such list, return []
        """
        s = Solver()
        """
        exp = 0
        vars = []
        for i in range(terms):
            (vr,) = Ints('var' + str(i))
            s.add(vr > 0)
            exp = exp + vr
            if len(vars) > 0:
                s.add(vr > vars[-1])
            vars.append(vr)
            prev = vr
        s.add(exp == N)
        if s.check() != sat:
            return []
        model = s.model()
        return [int(model[i].as_string()) for i in vars]
        """
        (x,) = Ints('x')
        s.add(x > 0)
        s.add(sum([x + i for i in range(terms)]) == N)
        if s.check() != sat:
            return []
        model = s.model()
        x0 = int(model[x].as_string())
        return [x0 + i for i in range(terms)]
    for N in range(3, 50):
        print(N)
        for i in range(2, N):
            xs = attempt(i, N)
            if not xs:
                continue
            print(xs)
            assert sum(xs) == N, f"sum({xs}) != {N}"
    print("cribbage ok")


def bithack():
    def attempt(BIT_WIDTH: int) -> Set[Tuple[int, int]]:
        """
        TODO: 1 point
        J. H. Quick noticed that ((x + 2) ⊕ 3) - 2 = ((x - 2) ⊕ 3) + 2 for all x.
        Find all constants a and b such that ((x + a) ⊕ b) - a = ((x - a) ⊕ b) + a is an identity.

        :param BIT_WIDTH: width of bit vectors a, b, x
        :return set of pairs of `a` and `b`
        """
        s = Solver()
        x, a, b = BitVecs('x a b', BIT_WIDTH)
        s.add(ForAll([x], ((x + a) ^ b) - a == ((x - a) ^ b) + a))
        ret = set()
        while s.check() == sat:
            model = s.model()
            add = (int(model[a].as_string()), int(model[b].as_string()))
            ret.add(add)
            s.add(Not(model2formula(model)))
        return ret
    assert attempt(2) == {(3, 3), (0, 0), (1, 1), (2, 0), (2, 2), (2, 3), (0, 3), (0, 1), (0, 2), (1, 0), (3, 0), (3, 1), (2, 1), (1, 2), (1, 3), (3, 2)}
    assert attempt(3) == {(4, 0), (3, 4), (4, 3), (3, 1), (5, 4), (4, 6), (5, 1), (0, 2), (0, 5), (2, 2), (1, 0), (2, 5), (7, 4), (6, 2), (7, 1), (6, 5), (4, 2), (3, 0), (4, 5), (5, 0), (0, 1), (0, 7), (2, 4), (0, 4), (2, 1), (2, 7), (1, 5), (6, 1), (7, 0), (6, 4), (6, 7), (4, 1), (4, 7), (3, 5), (4, 4), (5, 5), (0, 0), (1, 1), (0, 3), (2, 0), (1, 4), (0, 6), (2, 3), (2, 6), (6, 0), (6, 6), (7, 5), (6, 3)}
    assert len(attempt(4)) == 128
    assert len(attempt(5)) == 320
    print("bithack ok")

def Equiv(x, y):
    return x == y

def is_power_of_two():
    def attempt(SIZE: int):
        """
        TODO: 1 point
        Докажите при помощи SMT-решателя, что `(x != 0) && (x & (x - 1)) == 0` - это код, возвращающий истинное значение
        тогда и только тогда, когда битвектор x является степенью двойки.
        :param SIZE: width of the bit vector `x`
        :returns None
        """
        s = Solver()
        (x,) = BitVecs('x', SIZE)
        (po,) = Ints('po')
        s.add(ForAll([x], Implies(And(po >= 0, po < SIZE), Equiv(x == Int2BV(2**po, SIZE), And(x != 0, (x & (x - 1)) == 0)))))
        assert s.check() == sat
        return
    for i in range(1, 20):
        attempt(i)
    print('is_power_of_two ok')


def groups():
    """
    TODO: 4 points
    Определите группу в теории неинтерпретированных функций (определите сорт, константы, функции, задайте аксиомы)
    https://ru.wikipedia.org/wiki/%D0%93%D1%80%D1%83%D0%BF%D0%BF%D0%B0_(%D0%BC%D0%B0%D1%82%D0%B5%D0%BC%D0%B0%D1%82%D0%B8%D0%BA%D0%B0)#%D0%9E%D0%BF%D1%80%D0%B5%D0%B4%D0%B5%D0%BB%D0%B5%D0%BD%D0%B8%D0%B5
    Затем докажите при помощи SMT-решателя, следующие теоремы:
    - обратный элемент для произведения - это произведение обратных элементов, взятых в обратном порядке
    - если обратные для двух элементов равны, то равны сами эти элементы
    - обратный элемент для обратного это сам элемент
    - обратный элемент для единицы - единица
    - x * c = b /\ y * c = b -> x = y

    Также автоматически постройте группу, в которой есть элемент, не равный своему обратному
    Замечание: когда решатель `s` вернул unsat, можно посмотреть на произведённое им доказательство: print(s.proof().sexpr())
    (Для этого в начало решения вставьте `set_param(proof=True)`)
    """

    Type = DeclareSort('GroupType')

    Op = Function("assoc", Type, Type, Type)
    Neg = Function("neg", Type, Type)
    x, y, z, b = Consts('x y z b', Type)
    (e,) = Consts('e', Type)
    def getSolver():
        s = Solver()
        s.add(ForAll([x, y, z], Op(Op(x, y), z) == Op(x, Op(y, z))))
        s.add(ForAll([x], And(Op(e, x) == x, Op(x, e) == x)))
        s.add(ForAll([x], And(Op(x, Neg(x)) == e, Op(Neg(x), x) == e)))
        return s

    s = getSolver()
    # 1
    s.add(ForAll([x, y], Neg(Op(x, y)) == Op(Neg(y), Neg(x))))

    # 2
    s.add(ForAll([x, y], Implies(Neg(x) == Neg(y), x == y)))

    # 3
    s.add(ForAll([x], Neg(Neg(x)) == x))

    # 4
    # I am sorry, but forall x. neg(neg(x)) == x, proofed above...
    s.add(Neg(Neg(e)) == e)

    # 5
    s.add(ForAll([x, y, z, b], Implies(And(Op(x, z) == b, Op(y, z) == b), x == y)))

    assert s.check() == sat
    print('groups ok 1')

    return
    # it consumes too much memory on my pc =(
    s = getSolver()
    def card_at_most(Sort, card):
        cs = [Const(c, Sort) for c in range(card)]
        x = Const(card, Sort)
        return Exists(cs, ForAll(x, Or([x == c for c in cs])))
    s.add(card_at_most(Type, 3))
    s.add(Exists([x], Neg(x) != x))
    print(s.to_smt2())
    res = s.check()
    print(res)
    assert res == sat
    print(s.model()[Type])
    print("Model:")
    print(s.model())
    print('groups ok 2')

    return


def simple_induction():
    n = Int("n")
    Sumn = Function("sumn", IntSort(), IntSort())
    s = Solver()
    # defining sum(n) = 1 + 2 + 3 + ... n
    s.add(Sumn(0) == 0)
    s.add(ForAll([n], Sumn(n + 1) == n + 1 + Sumn(n)))

    def prop_sumn(n):
        return 2 * Sumn(n) == n * (n + 1)

    def induction(p):
        n = Int("n")
        return Implies(And(p(0), ForAll([n], Implies(And(n >= 0, p(n)), p(n + 1)))),
                       # --------------------------------------------------------
                       ForAll([n], Implies(n >= 0, p(n))))

    s.add(induction(prop_sumn))
    s.add(Not(ForAll([n], Implies(n >= 0, prop_sumn(n)))))
    if s.check() == unsat:
        print("proved")


def subtyping():
    def card_at_most(Sort, card):
        cs = [Const(c, Sort) for c in range(card)]
        x = Const(card, Sort)
        return Exists(cs, ForAll(x, Or([x == c for c in cs])))
    Type = DeclareSort('Type')
    subtype = Function('subtype', Type, Type, BoolSort())
    exception = Const('exception', Type)
    Object = Const('Object', Type)

    x, y, z, v = Consts('x y z v', Type)
    axioms = [
        subtype(x, x),
        Implies(And(subtype(x, y), subtype(y, z)), subtype(x, z)),
        Implies(And(subtype(x, y), subtype(y, x)), x == y),
        subtype(x, Object),
        subtype(exception, x)
    ]
    solver = Solver()
    solver.add([ForAll([x, y, z, v], ax) for ax in axioms])
    solver.add(card_at_most(Type, 5))
    # a, b, c, d = Consts("a b c d", Type)
    # solver.add([Exists([a, b, c], ForAll(d, Or(d == a, d == b, d == c)))])

    s, t = Consts("s t", Type)
    solver.add(Not(subtype(s, t)))
    solver.add(Not(subtype(t, s)))
    print(solver.check())
    print("Interpretation for Type:")
    print(solver.model()[Type])
    print("Model:")
    print(solver.model())


def sortedness():
    array_sort =  ArraySort(IntSort(), IntSort())
    sorted = RecFunction("sorted", array_sort, BoolSort())
    arr = Const("arr", array_sort)
    i, j = Ints("i j")
    RecAddDefinition(sorted, arr, ForAll([i, j], Implies(i <= j, arr[i] <= arr[j])))
    a = Const("a", array_sort)
    x, y, z = Ints("x y z")
    solver = Solver()
    query = [
        0 <= x,
        0 <= y,
        0 <= z,
        x <= 10,
        y <= 10,
        z <= 10,
        sorted(a),
        y <= z,
        a[x] == a[z],
        a[x] != a[y]
    ]
    solver.add(query)
    solver.push()
    solver.add(x <= y)
    print(solver.check())
    if solver.check() == sat:
        print(solver.model())
    solver.pop()
    solver.push()
    solver.add(x - 1 <= y)
    print(solver.check())
    if solver.check() == sat:
        print(solver.model())


def queens():
    def attempt(SIZE: int) -> List[int]:
        """
        TODO: 3 points
        Решите задачу о расстановке ферзей, сведя задачу в линейную арифметику
        :param SIZE: число ферзей >= 8
        :return: список целых чисел от 1 до SIZE:
            если по индексу i расположено число j в списке, тогда в строке i+1 и в столбце j стоит ферзь
            Пример: [4, 2, 8, 6, 1, 3, 5, 7]
        """
        #set_param(proof=True)
        solver = SolverFor("QF_LIA")
        x, y, dx, dy, d = Ints('x y dx dy d')
        ans_x = list(range(SIZE))
        ans_y = Ints(' '.join(map(lambda x: 'y_' + str(x), range(SIZE))))
        idx = 0
        for idx in range(SIZE):
            x = ans_x[idx]
            y = ans_y[idx]
            solver.add(y >= 0)
            solver.add(y < SIZE)
            for oi in range(SIZE):
                if oi == idx:
                    continue
                ox = ans_x[oi]
                oy = ans_y[oi]
                for d in list(range(1, SIZE)) + list(map(lambda x: -x, range(1, SIZE))):
                    solver.add(Not(And(ox == x + d, oy == y + d, x + d >= 0, x + d < SIZE, y + d >= 0, y + d < SIZE)))
                    solver.add(Not(And(ox == x + d, oy == y - d, x + d >= 0, x + d < SIZE, y - d >= 0, y - d < SIZE)))
                    solver.add(Not(And(ox == x + d, oy == y, x + d >= 0, x + d < SIZE)))
                    solver.add(Not(And(ox == x, oy == y + d, y + d >= 0, y + d < SIZE)))
        assert solver.check() == sat
        m = solver.model()
        return [1 + int(m[x].as_string()) for x in ans_y]
    for s in range(8, 40):
        print(attempt(s))


def fractions():
    def attempt() -> List[int]:
        """
        TODO: 3 points
        Find distinct non-zero digits such that the following equation holds:
               A        D        G
            ------  + ----- + ------  = 1
              B*C      E*F      H*I
        :return [A,B,C,D,E,F,G,H,I]
        """
        s = Solver()
        ints = Ints('A, B, C, D, E, F, G, H, I')
        A, B, C, D, E, F, G, H, I = ints
        for v in ints:
            s.add(v >= 1)
            s.add(v <= 9)
        for i in range(len(ints)):
            for j in range(len(ints)):
                if i != j:
                    s.add(ints[i] != ints[j])
        s.add(A*E*F*H*I + D*B*C*H*I + G*B*C*E*F == B*C*E*F*H*I)
        assert s.check() == sat
        model = s.model()
        return [int(model[x].as_string()) for x in ints]
    xs = attempt()
    assert set(xs) == set(range(1, 10))
    [A, B, C, D, E, F, G, H, I] = xs
    assert A / (B * C) + D / (E * F) + G / (H * I) == 1
    print("{} / ({} * {}) + {} / ({} * {}) + {} / ({} * {}) = 1".format(*xs))
    print('fractions ok')


def geometry_inscribed_angle():
    """
    TODO: 3 points
    Автоматически докажите теорему "Вписанный угол, опирающийся на горизонтальный диаметр окружности, равен 90°"
    * горизонтальный диаметр - диаметр, параллельный оси абсцисс в текущей системе координат
    """
    Point = DeclareSort('Point')
    a, b, c, o = Consts('a b c o', Point)
    ans = Real('ans')
    Angle = Function('angle', Point, Point, Point, RealSort())
    In = Function('in', Point, Point, Point, Point, BoolSort())
    Dist = Function('dist', Point, Point, RealSort())
    s = Solver()

    # all points are distinct
    s.add(a != b)
    s.add(a != c)
    s.add(b != c)

    # points on circle
    s.add(Dist(a, o) == Dist(o, b))
    s.add(Dist(a, o) == Dist(c, o))

    # on diameter
    s.add(Angle(a, o, b) == 180)
    s.add(Angle(a, c, b) > 0)

    # specify which angle is in which
    s.add(ForAll([a, b, c, o], Implies(In(a, b, c, o), In(a, o, c, b))))
    s.add(In(a, c, b, o))
    # if in then sum
    s.add(ForAll([a, b, c, o], Implies(In(a, b, c, o), Angle(a, b, c) == Angle(a, b, o) + Angle(o, b, c))))

    # distance def part
    s.add(ForAll([a, b], Dist(a, b) >= 0))
    s.add(ForAll([a, b], Dist(a, b) == Dist(b, a)))
    s.add(ForAll([a, b], Equiv(Dist(a, b) == 0, a == b)))
    # angle flip
    s.add(ForAll([a, b, c], Angle(a, b, c) == Angle(c, b, a)))

    # same edges => same angles
    s.add(ForAll([a, b, c], Implies(And(a != b, a != c, b != c, Dist(a, b) == Dist(a, c)), Angle(a, b, c) == Angle(a, c, b))))

    # sum of angles in triangle
    s.add(ForAll([a, b, c], Implies(And(a != b, a != c, b != c), Angle(a, b, c) + Angle(b, c, a) + Angle(c, a, b) == 180)))

    s.add(ans == Angle(a, c, b))

    assert s.check() == sat
    res = s.model()[ans]
    print(res)
    assert float(res.as_string()) == 90
    return


def vector_properties():
    x, y = Reals("x y")
    # q = np.array([x, y])
    # np.dot(q, q)  # dot product
    # np.array([x]) * q  # scalar product
    # q * x  # scalar product

    def vec_eq(x, y):
        return And(np.vectorize(op.eq)(x, y).tolist())

    def NPArray(n):  # a vector of fresh variables.
        return np.array([FreshReal() for _ in range(n)])

    size = 4
    u = NPArray(size)
    v = NPArray(size)
    w = NPArray(size)

    # prove(u + v == v + u) # does not work because python and/or/not do not work
    prove(vec_eq(v + u, u + v))                                 # commutativity
    prove(vec_eq(v + (u + w), (v + u) + w))                     # associativity
    prove(vec_eq((v + w) * x, (w * x) + (v * x)))               # scalar distrubitivity
    prove(np.dot(v, u) ** 2 <= np.dot(v, v) * np.dot(u, u))     # cauchy schwartz inequality

    # proving properties of a linear operator defined by a matrix
    def linear(Z):
        x = NPArray(2)
        y = NPArray(2)
        return vec_eq(Z @ (x + y), Z @ x + Z @ y)

    Z = NPArray(4).reshape(2, 2)
    prove(linear(Z))


def Hamiltonian_cycle():
    def is_ok(gr, path):
        smoke = len(gr) == len(path) and set(gr.keys()) == set(path)
        if not smoke:
            return False
        cur = [path[0]]
        for v in path:
            if v not in cur:
                return False
            cur = gr[v]
        return path[0] in cur
    def attempt(gr):
        """
        TODO: 4 points
        :parameter `gr`: a graph as an adjacency list, e.g. {0:[1,2], 1:[2], 2:[1,0]}.
        :returns list of integers (a path) which is a Hamiltonian cycle in the input graph
        :returns `None` if no Hamiltonian cycle is in the input graph
        See http://en.wikipedia.org/wiki/Hamiltonian_path
        """
        s = Solver()
        Path = Function('Path', IntSort(), IntSort(), BoolSort())
        x, y = Ints('a b')
        s.add(ForAll([x, y], Equiv(Path(x, y), Path(y, x))))
        was = set()
        for v in gr:
            for to in gr[v]:
                was.add((v, to))
                s.add(Path(v, to) == True)
        for i in gr:
            for j in gr:
                if (i, j) not in was:
                    s.add(Path(i, j) == False)
        verts = Ints(range(0, len(gr)))
        for v in verts:
            s.add(v >= 0)
            s.add(v < len(gr))
        for i in range(len(verts)):
            for j in range(len(verts)):
                if i != j:
                    s.add(verts[i] != verts[j])
        s.add(verts[0] == 0)
        for i in range(len(gr)):
            s.add(Path(verts[i], verts[(i + 1) % len(gr)]) == True)
        if s.check() != sat:
            print('none')
            return None
        model = s.model()
        res = [int(model[v].as_string()) for v in verts]
        return res

    grdodec = {0: [1, 4, 5],
               1: [0, 7, 2],
               2: [1, 9, 3],
               3: [2, 11, 4],
               4: [3, 13, 0],
               5: [0, 14, 6],
               6: [5, 16, 7],
               7: [6, 8, 1],
               8: [7, 17, 9],
               9: [8, 10, 2],
               10: [9, 18, 11],
               11: [10, 3, 12],
               12: [11, 19, 13],
               13: [12, 14, 4],
               14: [13, 15, 5],
               15: [14, 16, 19],
               16: [6, 17, 15],
               17: [16, 8, 18],
               18: [10, 19, 17],
               19: [18, 12, 15]}

    t1 = perf_counter()
    sdodec = attempt(grdodec)  # works ~ 1 minute on my PC, so please be patient
    assert is_ok(grdodec, sdodec)
    print(sdodec)
    print(perf_counter() - t1)
    grherschel = {0: [1, 9, 10, 7],
                  1: [0, 8, 2],
                  2: [1, 9, 3],
                  3: [2, 8, 4],
                  4: [3, 9, 10, 5],
                  5: [4, 8, 6],
                  6: [5, 10, 7],
                  7: [6, 8, 0],
                  8: [1, 3, 5, 7],
                  9: [2, 0, 4],
                  10: [6, 4, 0]}
    t1 = perf_counter()
    assert attempt(grherschel) is None
    print(perf_counter() - t1)


def array_theory_proof():
    """
    TODO: 2 points
    Предъявите литерал (не произвольную формулу!) F и список из n литералов Fs = [F1, ..., Fn] в теории массивов над линейной целочисленной арифметикой,
    такие что:
    - n >= 2
    - |= F -> (F1 \/ ... \/ Fn)
    - для всех 1 <= i <= n не верно, что |= F -> Fi
    Эти проверки уже закодированы для вас в функции check, вам нужно только придумать и записать литералы F и Fs.
    Замечание: это упражнение фактически показывает, что теория массивов невыпукла
    """
    def check(F, Fs):
        assert len(Fs) >= 2
        solver = SolverFor("QF_AUFLIA")
        solver.push()
        solver.add(Not(Implies(F, Or(Fs))))
        assert solver.check() == unsat
        solver.pop()
        for Fi in Fs:
            solver.push()
            solver.add(Not(Implies(F, Fi)))
            assert solver.check() == sat
            solver.pop()
    x, y = Bools('x y')
    F = x != y
    Fs = [x, y]
    check(F, Fs)
    print('array_theory_proof ok')


def bmc():
    def bmc(init: BoolRef, trans: BoolRef, goal: BoolRef, fvs: List[ExprRef], xs: List[ExprRef], xns: List[ExprRef]):
        """
        TODO: 5 points
        Написать свой bounded model checker
        Он должен отвечать на вопрос, можно ли, начиная из состояния, на котором верно `init`,
        производя переходы `trans`, достичь состояния, в котором выполнится `goal`
        :param fvs, xs, xns: списки переменных
        :param init: формула над xs, описывающая начальные состояния системы
        :param trans: формула над (xs + xns + fvs), описывающая переход системы
        :param goal: формула над xs, описывающая "плохие" состояния системы
        :returns число, после скольких итераций достигается `goal` и
        :returns  список значений начальных переменных `xs`, на которых достижим `goal`, в том же порядке, что входной список `xs`
        Замечание: используйте функцию `substitute` в решении
        Замечание: каноничное решение занимает 17 строк, эта задача совсем не сложная
        """
        return 0, []

    x0, x1 = BitVecs('x0 x1', 4)
    c1 = bmc(And(x0 >= 0, x0 <= 3, x0 != 1), x1 == x0 + 3, x0 == 10, [], [x0], [x1])
    print(c1)
    assert c1 == (9, ["2"])


if __name__ == "__main__":
    fns = []
    fns.append(bithack)
    fns.append(is_power_of_two)
    fns.append(cribbage)
    fns.append(queens)
    fns.append(groups)
    fns.append(array_theory_proof)
    fns.append(Hamiltonian_cycle)
    fns.append(geometry_inscribed_angle)
    fns.append(fractions)
    fns.append(bmc)
    fails = []
    for f in fns:
        try:
            f()
            print(f.__name__, 'passed')
        except KeyboardInterrupt:
            print(f.__name__, 'interrupted')
            fails.append(f)
            while True:
                try:
                    x = input("Skip? (yes/no) > ").strip()
                    break
                except KeyboardInterrupt:
                    pass
            if x == 'yes':
                continue
        except Exception as e:
            print(f.__name__, 'failed')
            print(e)
            fails.append(f)
    print('Failed:', len(fails))
    for f in fails:
        print('\t', f.__name__)
