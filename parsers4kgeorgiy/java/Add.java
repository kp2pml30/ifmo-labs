package expression;

import expression.generic.NumberWrapper;

public class Add<T> extends BinaryOperator<T> {
    public Add(CommonExpression<T> left, CommonExpression<T> right) {
        super(left, right);
    }

    @Override
    protected NumberWrapper<T> calculateOperand(NumberWrapper<T> left, NumberWrapper<T> right) {
        return left.add(right);
    }

    @Override
    protected String getOperatorSign() {
        return "+";
    }

    @Override
    public OperatorPriority getOperatorPriority() {
        return OperatorPriority.ADDGROUP;
    }

    public static class MyProvider<T> extends Provider<T> {
        @Override
        public BinaryOperator<T> provide(CommonExpression<T> left, CommonExpression<T> right) {
            return new Add<T>(left, right);
        }
        @Override
        public int getOperatorPriority() {
           return OperatorPriority.ADDGROUP.getValue();
        }
    }

    @Override
    public boolean isAssoc() {
        return true;
    }
}
