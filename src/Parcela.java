import java.time.LocalDate;

public class Parcela {

    private /*@ spec_public @*/ int numero;
    private /*@ spec_public @*/ double valor;
    private /*@ spec_public @*/ LocalDate dataVencimento;
    private /*@ spec_public @*/ boolean paga;
    private /*@ spec_public @*/ /*@ nullable @*/ LocalDate dataPagamento;

    //@ public invariant numero > 0;
    //@ public invariant valor > 0;
    //@ public invariant dataVencimento != null;
    //@ public invariant paga ==> dataPagamento != null;
    //@ public invariant !paga ==> dataPagamento == null;

    //@ requires num > 0;
    //@ requires val > 0;
    //@ requires vencimento != null;
    //@ ensures this.numero == num;
    //@ ensures this.valor == val;
    //@ ensures this.dataVencimento.equals(vencimento);
    //@ ensures !this.paga;
    //@ ensures this.dataPagamento == null;
    //@ pure
    public Parcela(int num, double val, LocalDate vencimento) {
        this.numero = num;
        this.valor = val;
        this.dataVencimento = vencimento;
        this.paga = false;
        this.dataPagamento = null;
    }

    //@ ensures \result == numero;
    //@ ensures \result > 0;
    //@ pure
    public int getNumero() {
        return numero;
    }

    //@ ensures \result == valor;
    //@ ensures \result > 0;
    //@ pure
    public double getValor() {
        return valor;
    }

    //@ ensures \result == dataVencimento;
    //@ ensures \result != null;
    //@ pure
    public LocalDate getDataVencimento() {
        return dataVencimento;
    }

    //@ ensures \result == paga;
    //@ pure
    public boolean isPaga() {
        return paga;
    }

    //@ ensures \result == dataPagamento;
    //@ ensures paga ==> \result != null;
    //@ ensures !paga ==> \result == null;
    //@ pure
    public /*@ nullable @*/ LocalDate getDataPagamento() {
        return dataPagamento;
    }

    //@ requires !paga;
    //@ assignable paga, dataPagamento;
    //@ ensures paga;
    //@ ensures dataPagamento != null;
    public void marcarComoPaga() {
        this.paga = true;
        this.dataPagamento = LocalDate.now();
    }

    //@ ensures \result >= 0;
    //@ ensures paga ==> \result == 0;
    //@ pure
    public double calcularMultaAtraso() {
        if (paga || LocalDate.now().isBefore(dataVencimento)) {
            return 0;
        }

        long diasAtraso = java.time.temporal.ChronoUnit.DAYS.between(
                dataVencimento, LocalDate.now()
        );

        double multa = valor * 0.02;
        double juros = valor * 0.001 * diasAtraso;

        return multa + juros;
    }

    //@ ensures \result >= valor;
    //@ ensures \result == valor + calcularMultaAtraso();
    //@ pure
    public double getValorTotal() {
        return valor + calcularMultaAtraso();
    }
}
