package expression;

import expression.exceptions.EvaluationException;
import expression.generic.NumberWrapper;

public abstract class BinaryOperator<T> implements CommonExpression<T> {
    protected final CommonExpression<T> left, right;

    public static abstract class Provider<T> {
        public abstract BinaryOperator<T> provide(CommonExpression<T> left, CommonExpression<T> right);
        public abstract int getOperatorPriority();
    }

    public BinaryOperator(final CommonExpression<T> left, final CommonExpression<T> right) {
        if (left == null || right == null) {
            throw new IllegalArgumentException("Binary operator constructed from null");
        }
        this.left = left;
        this.right = right;
    }

    public abstract OperatorPriority getOperatorPriority();
    protected abstract NumberWrapper<T> calculateOperand(NumberWrapper<T> left, NumberWrapper<T> right);
    protected abstract String getOperatorSign();
    public abstract boolean isAssoc();
    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x) {
        return calculateOperand(left.evaluate(x), right.evaluate(x));
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x, NumberWrapper<T> y, NumberWrapper<T> z) {
        return calculateOperand(left.evaluate(x, y, z), right.evaluate(x, y, z));
    }

    @Override
    public void toString(StringBuilder builder) {
        builder.append('(');
        builder.append(left.toString());
        builder.append(" " + getOperatorSign() + " ");
        builder.append(right.toString());
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
        if (BinaryOperator.class.isAssignableFrom(left.getClass())) {
            BinaryOperator<T> l = (BinaryOperator<T>)left;
            if (l.getOperatorPriority().getValue() < getOperatorPriority().getValue()) {
                builder.append('(');
                builder.append(l.toMiniString());
                builder.append(')');
            } else {
                l.toMiniString(builder);
            }
        } else {
            builder.append(left.toMiniString());
        }
        builder.append(" " + getOperatorSign() + " ");
        if (right instanceof BinaryOperator) {
            BinaryOperator<T> r = (BinaryOperator<T>)right;
            final Class<?>
                rclass = r.getClass(),
                mclass = getClass();
            final int
                rprior = r.getOperatorPriority().getValue(),
                mprior = getOperatorPriority().getValue();
            if (rprior > mprior ||
                    rprior == mprior && (mclass.equals(rclass) && isAssoc() ||
                                                             BinaryMinifier.mayBeMinified(mclass, rclass))) {
                r.toMiniString(builder);
            } else {
                builder.append('(');
                r.toMiniString(builder);
                builder.append(')');
            }
        } else {
            builder.append(right.toMiniString());
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null || !getClass().equals(obj.getClass()) || !left.equals(((BinaryOperator)obj).left) || !right.equals(((BinaryOperator)obj).right)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        // return toString().hashCode();
        return (left.hashCode() * 31 + (right.hashCode() * 31 ^ 127)) ^ getOperatorSign().hashCode();
    }

    protected void error(EvaluationException exception) {
      exception.setWhere(this);
      throw exception;
    }
}

