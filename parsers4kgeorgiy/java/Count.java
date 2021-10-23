package expression;

import expression.generic.NumberWrapper;

public class Count<T> extends UnaryOperator<T> {
    public static class MyProvider<T> extends Provider<T> {
        @Override
        public UnaryOperator<T> provide(CommonExpression<T> child) {
            return new Count<T>(child);
        }
    }

    public Count(CommonExpression<T> body) {
        super(body);
    }

    @Override
    protected NumberWrapper<T> calculateOperand(NumberWrapper<T> me) {
        return me.count();
    }

    @Override
    protected String getOperatorSign() {
        return "count ";
    }
}
