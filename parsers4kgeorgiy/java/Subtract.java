package expression;

import expression.generic.NumberWrapper;

public class Subtract<T> extends BinaryOperator<T> {
    public Subtract(CommonExpression<T> left, CommonExpression<T> right) {
        super(left, right);
    }

    @Override
    protected NumberWrapper<T> calculateOperand(NumberWrapper<T> left, NumberWrapper<T> right) {
        return left.subtract(right);
    }

    @Override
    protected String getOperatorSign() {
        return "-";
    }

    @Override
    public OperatorPriority getOperatorPriority() {
        return OperatorPriority.ADDGROUP;
    }

    @Override
    public boolean isAssoc() {
        return false;
    }

    public static class MyProvider<T> extends Provider<T> {
        @Override
        public BinaryOperator<T> provide(CommonExpression<T> left, CommonExpression<T> right) {
            return new Subtract<T>(left, right);
        }
        @Override
        public int getOperatorPriority() {
            return OperatorPriority.ADDGROUP.getValue();
        }
    }
}
