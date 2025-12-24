public class ValidacaoException extends Exception {

    //@ public invariant getMessage() != null;

    //@ requires message != null;
    //@ ensures getMessage().equals(message);
    //@ pure
    public ValidacaoException(String message) {
        super(message);
    }
}
