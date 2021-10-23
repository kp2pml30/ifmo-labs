package expression;

import expression.generic.NumberWrapper;

public class Const<T> implements Value<T> {
    private NumberWrapper<T> value;
    public Const(NumberWrapper<T> value) {
        this.value = value;
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> f) {
        return value;
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x, NumberWrapper<T> y, NumberWrapper<T> z) {
        return evaluate(x);
    }

    @Override
    public String toString() {
        return value.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null || !getClass().equals(obj.getClass())) {
            return false;
        }
        return value.equals(((Const)obj).value);
    }

    @Override
    public int hashCode() {
        return value.hashCode();
    }
}
