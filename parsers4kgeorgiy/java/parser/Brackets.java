package expression.parser;

import expression.CommonExpression;
import expression.generic.NumberWrapper;

public class Brackets<T> implements CommonExpression<T> {
    private boolean open;
    public Brackets(boolean opened) {
        open = opened;
    }

    public boolean isOpen() {
        return open;
    }

    @Override
    public void toString(StringBuilder builder) {
        throw new UnsupportedOperationException("");
    }

    @Override
    public void toMiniString(StringBuilder builder) {
        throw new UnsupportedOperationException("");
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x) {
        throw new UnsupportedOperationException("");
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x, NumberWrapper<T> y, NumberWrapper<T> z) {
        throw new UnsupportedOperationException("");
    }
}
