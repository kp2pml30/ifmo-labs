package expression;

public class Digits extends UnaryOperator {
    public static class MyProvider extends Provider {
        @Override
        public UnaryOperator provide(CommonExpression child) {
            return new Digits(child);
        }
    }

    public Digits(CommonExpression body) {
        super(body);
    }

    @Override
    protected int calculateOperand(int me) {
        int sum = 0;
        while (me != 0) {
            sum += me % 10;
            me /= 10;
        }
        return Math.abs(sum);
    }

    @Override
    protected String getOperatorSign() {
        return "digits ";
    }
}
