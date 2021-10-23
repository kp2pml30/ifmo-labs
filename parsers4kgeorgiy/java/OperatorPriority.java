package expression;

public enum OperatorPriority {
    MINGROUP(0),
    ADDGROUP(1),
    MULGROUP(2),
    POWGROUP(3);
    private int value;

    private OperatorPriority(int value) {
        this.value = value;
    }

    public int getValue() {
        return value;
    }
}
