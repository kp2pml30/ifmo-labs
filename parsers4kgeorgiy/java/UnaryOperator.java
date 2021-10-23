package expression;

import expression.generic.NumberWrapper;

public abstract class UnaryOperator<T> implements CommonExpression<T> {
    public static abstract class Provider<T> {
        public abstract UnaryOperator<T> provide(CommonExpression<T> child);
    }

    protected CommonExpression<T> body;

    public UnaryOperator(CommonExpression<T> body) {
        if (body == null) {
            throw new IllegalArgumentException("Unary opertor null body");
        }
        this.body = body;
    }

    protected abstract String getOperatorSign();
    protected abstract NumberWrapper<T> calculateOperand(NumberWrapper<T> me);

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x) {
        return calculateOperand(body.evaluate(x));
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x, NumberWrapper<T> y, NumberWrapper<T> z) {
        return calculateOperand(body.evaluate(x, y, z));
    }

    @Override
    public void toString(StringBuilder builder) {
        builder.append(getOperatorSign());
        builder.append('(');
        builder.append(body.toString());
        builder.append(')');
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        toString(builder);
        return builder.toString();
    }

    @Override
    public void toMiniString(StringBuilder builder) {
        builder.append(getOperatorSign());
        if (BinaryOperator.class.isAssignableFrom(body.getClass())) {
            builder.append('(');
            builder.append(body.toMiniString());
            builder.append(')');
        } else {
            builder.append(body.toMiniString());
        }
    }
}
