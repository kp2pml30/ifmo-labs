package expression;

import expression.generic.NumberWrapper;

public interface TripleExpression<T> extends ToMiniString {
    NumberWrapper<T> evaluate(NumberWrapper<T> x, NumberWrapper<T> y, NumberWrapper<T> z);
}
