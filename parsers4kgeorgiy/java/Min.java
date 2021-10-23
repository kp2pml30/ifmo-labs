package expression;

import expression.generic.NumberWrapper;

public class Min<T> extends BinaryOperator<T> {
    public Min(CommonExpression<T> left, CommonExpression<T> right) {
        super(left, right);
    }

    @Override
    protected NumberWrapper<T> calculateOperand(NumberWrapper<T> left, NumberWrapper<T> right) {
        return left.min(right);
    }

    @Override
    protected String getOperatorSign() {
        return " min ";
    }

    @Override
    public OperatorPriority getOperatorPriority() {
        return OperatorPriority.MINGROUP;
    }

    public static class MyProvider<T> extends Provider<T> {
        @Override
        public BinaryOperator<T> provide(CommonExpression<T> left, CommonExpression<T> right) {
            return new Min<T>(left, right);
        }
        @Override
        public int getOperatorPriority() {
           return OperatorPriority.MINGROUP.getValue();
        }
    }

    @Override
    public boolean isAssoc() {
        return true;
    }
}
