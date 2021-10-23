package expression;

import expression.generic.NumberWrapper;

public class Multiply<T> extends BinaryOperator<T> {
    public Multiply(CommonExpression<T> left, CommonExpression<T> right) {
        super(left, right);
    }

    @Override
    protected NumberWrapper<T> calculateOperand(NumberWrapper<T> left, NumberWrapper<T> right) {
        return left.multiply(right);
    }

    @Override
    protected String getOperatorSign() {
        return "*";
    }

    @Override
    public OperatorPriority getOperatorPriority() {
        return OperatorPriority.MULGROUP;
    }

    @Override
    public boolean isAssoc() {
        return true;
    }
    public static class MyProvider<T> extends Provider<T> {
        @Override
        public BinaryOperator<T> provide(CommonExpression<T> left, CommonExpression<T> right) {
            return new Multiply<T>(left, right);
        }
        @Override
        public int getOperatorPriority() {
           return OperatorPriority.MULGROUP.getValue();
        }
    }
}
