package expression;

import expression.generic.NumberWrapper;

public interface Expression<T> extends ToMiniString {
    NumberWrapper<T> evaluate(NumberWrapper<T> x);
}
