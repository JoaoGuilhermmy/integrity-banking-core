public class SaldoInsuficienteException extends Exception {

    //@ public invariant getMessage() != null;

    //@ requires message != null;
    //@ ensures getMessage().equals(message);
    //@ pure
    public SaldoInsuficienteException(String message) {
        super(message);
    }
}
