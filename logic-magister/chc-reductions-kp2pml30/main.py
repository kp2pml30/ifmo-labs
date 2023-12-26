from z3 import *
from typing import *

# wrapper to solve CHC constraints and extract result
def solve_horn(chc):
    s = z3.SolverFor('HORN')
    s.set('engine', 'spacer')
    s.set('proof', True)

    s.set('xform.inline_eager', False)
    s.set('xform.inline_linear', False)
    s.set('xform.slice', False)

    # add constraints to solver
    s.add(chc)

    # run solver
    res = s.check()
    # extract model or proof
    answer = None
    if res == z3.sat:
        answer = s.model()
    elif res == z3.unsat:
        answer = s.proof()
    return res, answer

##################################################

def mc91(n: int) -> int:
    if n > 100:
        return n - 10
    else:
        return mc91(mc91(n + 11))

"""
Доказать, что `x <= 100 => mc91(x) = 91` для любых x
"""
def example_mc91() -> CheckSatResult:
    mc_91 = Function("mc_91", IntSort(), IntSort(), BoolSort())

    n = Int("n")
    tmp = Int("tmp")
    res = Int("res")

    rule_1 = ForAll([n, res], Implies(n > 100, mc_91(n, n - 10)))
    rule_2 = ForAll([n, tmp, res], Implies(And(n <= 100, mc_91(n + 11, tmp), mc_91(tmp, res)), mc_91(n, res)))

    query = ForAll([n, res], Implies(And(mc_91(n, res), n <= 100, res != 91), False))

    chc = [
        rule_1,
        rule_2,
        query
    ]

    #print(chc)

    (status, model) = solve_horn(chc)
    assert status == sat
    print(model)

    return status

##################################################

def function_1(x: int, y: int, z1: int, z2: int) -> Tuple[int, int]:
    i = 0
    while i < x:
        i = i + 1
        z1 = z1 + y

    i = 0
    while i < x:
        i = i + 1
        z2 = z2 + y

    return z1, z2

def my_loop(to, updater, app_vars=[]):
    i = FreshInt("i")
    res = FreshInt("res")
    accum = FreshInt("accum")
    # i accum res
    loop = FreshFunction(IntSort(), IntSort(), IntSort(), *[x.sort() for x in app_vars], BoolSort())
    rules = []
    rules.append(ForAll(app_vars + [i, accum, res], Implies(And(i < to, loop(i, accum, res, *app_vars)), loop(i + 1, updater(accum), res, *app_vars))))
    rules.append(ForAll(app_vars + [i, accum], Implies(i >= to, loop(i, accum, accum, *app_vars))))
    return loop, rules


"""
Доказать, что если

a = b

то после выполнения функции

c, d = function_1(x, y, a, b)

будет выполняться

c = d

для любых x, y, a, b
"""
def task_1() -> CheckSatResult:
    x, y, z1, z2, rz1, rz2 = Ints("x y z1 z2 rz1 rz2")
    app_vars=[x, y]
    loop1, rules1 = my_loop(x, lambda x: x + y, app_vars=app_vars)
    loop2, rules2 = my_loop(x, lambda x: x + y, app_vars=app_vars)

    chc = rules1 + rules2
    chc += [
        ForAll(
            [x, y, z1, z2, rz1, rz2],
            Implies(
                And(z1 == z2, loop1(0, z1, rz1, *app_vars), loop2(0, z2, rz2, *app_vars), rz1 != rz2),
                False)
        )
    ]

    (status, model) = solve_horn(chc)
    assert status == sat, str(status) + " " + str(model)
    print(model)

    return status

##################################################

def ack(m: int, n: int) -> int:
    if m == 0:
        return n + 1
    elif n == 0:
        return ack(m - 1, 1)
    else:
        return ack(m - 1, ack(m, n - 1))


"""
Доказать, что если

m >= 0 && n >= 0

то

ack(m, n) >= n

"""
def task_2() -> CheckSatResult:
    ack = Function("ack", IntSort(), IntSort(), IntSort(), BoolSort())
    m, n, res, tmp = Ints("m n res tmp")
    chc = [
        ForAll([m, n], Implies(m == 0, ack(m, n, n + 1))),
        ForAll([m, n, res], Implies(And(n == 0, ack(m - 1, 1, res)), ack(m, n, res))),
        ForAll([m, n, res, tmp], Implies(And(m != 0, n != 0, ack(m, n - 1, tmp), ack(m - 1, tmp, res)), ack(m, n, res))),
        ForAll([m, n, res], Implies(And(m >= 0, m >= 0, ack(m, n, res), res < n), False)),
    ]
    (status, model) = solve_horn(chc)
    assert status == sat, str(status) + str(model)
    print(model)

    return status

##################################################

def recursiveSimple(a: int, b: int) -> int:
    if a < 0:
        raise Exception("A is not positive")

    if b < 0:
        raise Exception("B is not positive")

    if a < b:
        res = a
    elif a > b:
        res = recursiveSimple(a - 1, b)
    else:
        res = recursiveSimple(a - 1, b - 2)

    if res < 17:
        raise Exception("Res is not ok")

    return res

"""
Найти предусловие для функции recursiveSimple, при выполнении которого
функция НЕ завершается с исключением
"""
def task_3() -> CheckSatResult:
    rec = Function("rec", IntSort(), IntSort(), IntSort(), BoolSort())
    a, b, res, res2 = Ints("a b res res2")
    isOk = Function("isOk", IntSort(), IntSort(), BoolSort())
    chc = [
        # threw <=> can not not throw
        #ForAll([a, b, res], Implies(rec(a, b, res, True), Not(rec(a, b, res, False)))),
        #ForAll([a, b, res], Implies(rec(a, b, res, False), Not(rec(a, b, res, True)))),

        # threw <=> any result
        #ForAll([a, b, res, res2], Implies(rec(a, b, res, True), rec(a, b, res2, True))),

        # rec function
        ForAll([a, b], Implies(a < 0, Not(rec(a, b, 0)))),
        ForAll([a, b], Implies(b < 0, Not(rec(a, b, 0)))),
        ForAll([a, b, res], Implies(And(a < b, a < 17), Not(rec(a, b, res)))),
        ForAll([a, b, res], Implies(And(a < b, a >= 17), rec(a, b, a))),
        ForAll([a, b, res], Implies(And(a > b, Not(rec(a - 1, b, res))), Not(rec(a, b, res)))),
        ForAll([a, b, res], Implies(And(a > b, rec(a - 1, b, res), res < 17), Not(rec(a, b, res)))),
        ForAll([a, b, res], Implies(And(a > b, rec(a - 1, b, res), res >= 17), rec(a, b, res))),
        ForAll([a, b, res], Implies(And(a == b, rec(a - 1, b - 2, res), res < 17), Not(rec(a, b, res)))),
        ForAll([a, b, res], Implies(And(a == b, rec(a - 1, b - 2, res), res >= 17), rec(a, b, res))),
        ForAll([a, b, res], Implies(And(a == b, Not(rec(a - 1, b - 2, res))), Not(rec(a, b, res)))),
        #ForAll([a, b, res, threw2], Implies(And(a == b, rec(a - 1, b - 2, res, threw2)), rec(a, b, res, Or(res < 17, threw2)))),

        # oki doki
        ForAll([a, b, res], Implies(isOk(a, b), rec(a, b, res))),
        ForAll([a, b, res], Implies(rec(a, b, res), isOk(a, b))),
        #rec(2, 4, 2),
    ]

    (status, model) = solve_horn(chc)
    assert status == sat, str(status) + " " + str(model)
    #print(model)
    print('isOk', model[isOk])

    return status

##################################################

def search_in_array(array: List[int], value: int) -> int:
    for i in range(0, len(array)):
        if array[i] == value:
            return i

    return -1

"""
Доказать, что после исполнения кода:

res = search_in_array(array, value)

всегда выполняется постусловие

res == -1 or (res >= 0 and res < len(array) and array[res] == value)

Подсказка: список можно представить двумя переменными: массив значений и его длина.
"""
def task_4() -> CheckSatResult:
    arr = Array('arr', IntSort(), IntSort())
    idx, l, val, res = Ints('i l val res')
    iterate = Function("iterate", idx.sort(), arr.sort(), l.sort(), val.sort(), res.sort(), BoolSort())
    chc = [
        ForAll([idx, l, arr, val],
            Implies(idx >= l, iterate(idx, arr, l, val, -1))),
        ForAll([idx, l, arr, val],
            Implies(And(idx >= 0, idx < l, arr[idx] == val), iterate(idx, arr, l, val, idx))),
        ForAll([idx, l, arr, val, res],
            Implies(And(idx >= 0, idx < l, arr[idx] != val, iterate(idx + 1, arr, l, val, res)), iterate(idx, arr, l, val, res))),

        ForAll([l, arr, val, res],
            Implies(
                And(
                    iterate(0, arr, l, val, res),
                    Not(Or(res == -1, And(res >= 0, res < l, arr[res] == val)))
                ),
                False)),
    ]

    (status, model) = solve_horn(chc)
    assert status == sat, str(status) + " " + str(model)
    #print(model)

    return status


##################################################

def grade():
    score = 0
    if example_mc91() == sat:
        score += 0

    if task_1() == sat:
        score += 1

    if task_2() == sat:
        score += 2

    if task_3() == sat:
        score += 3

    if task_4() == sat:
        score += 4

    print(f"Total points for this homework: {score}")

if __name__ == "__main__":
    grade()
