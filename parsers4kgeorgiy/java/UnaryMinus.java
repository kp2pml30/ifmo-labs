package expression;

import expression.generic.NumberWrapper;

public class UnaryMinus<T> extends UnaryOperator<T> {
    public static class MyProvider<T> extends Provider<T> {
        @Override
        public UnaryOperator<T> provide(CommonExpression<T> child) {
            return new UnaryMinus<T>(child);
        }
    }

    public UnaryMinus(CommonExpression<T> body) {
        super(body);
    }

    @Override
    protected NumberWrapper<T> calculateOperand(NumberWrapper<T> me) {
        return me.negate();
    }

    @Override
    protected String getOperatorSign() {
        return "-";
    }
}
