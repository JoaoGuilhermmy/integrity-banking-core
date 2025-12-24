import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Emprestimo {

    private /*@ spec_public @*/ double valorTotal;
    private /*@ spec_public @*/ double taxaJuros;
    private /*@ spec_public @*/ int numeroParcelas;
    private /*@ spec_public @*/ List<Parcela> parcelas;
    private /*@ spec_public @*/ Cliente cliente;
    private /*@ spec_public @*/ LocalDate dataContratacao;

    //@ public invariant valorTotal > 0;
    //@ public invariant taxaJuros >= 0;
    //@ public invariant numeroParcelas > 0;
    //@ public invariant parcelas != null;
    //@ public invariant parcelas.size() == numeroParcelas;
    //@ public invariant cliente != null;
    //@ public invariant dataContratacao != null;
    //@ public invariant (\forall int i; 0 <= i && i < parcelas.size(); parcelas.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < parcelas.size(); parcelas.get(i).getNumero() == i + 1);

    //@ requires valor > 0;
    //@ requires numParcelas > 0;
    //@ requires taxa >= 0;
    //@ requires cli != null;
    //@ ensures this.valorTotal == valor;
    //@ ensures this.numeroParcelas == numParcelas;
    //@ ensures this.taxaJuros == taxa;
    //@ ensures this.cliente == cli;
    //@ ensures this.dataContratacao != null;
    //@ ensures this.parcelas != null;
    //@ ensures this.parcelas.size() == numParcelas;
    //@ pure
    public Emprestimo(double valor, int numParcelas, double taxa, Cliente cli) {
        this.valorTotal = valor;
        this.numeroParcelas = numParcelas;
        this.taxaJuros = taxa;
        this.cliente = cli;
        this.dataContratacao = LocalDate.now();
        this.parcelas = new ArrayList<>();

        gerarParcelas();
    }

    //@ requires parcelas.size() == 0;
    //@ assignable parcelas;
    //@ ensures parcelas.size() == numeroParcelas;
    //@ ensures (\forall int i; 0 <= i && i < parcelas.size(); parcelas.get(i) != null);
    //@ ensures (\forall int i; 0 <= i && i < parcelas.size(); !parcelas.get(i).isPaga());
    private void gerarParcelas() {
        double montanteTotal = calcularMontanteComJuros();
        double valorParcela = montanteTotal / numeroParcelas;

        LocalDate dataVenc = dataContratacao.plusMonths(1);

        //@ maintaining 1 <= i && i <= numeroParcelas + 1;
        //@ maintaining parcelas.size() == i - 1;
        //@ maintaining (\forall int j; 0 <= j && j < parcelas.size(); parcelas.get(j) != null);
        //@ loop_writes i, parcelas, dataVenc;
        //@ decreases numeroParcelas - i + 1;
        for (int i = 1; i <= numeroParcelas; i++) {
            Parcela p = new Parcela(i, valorParcela, dataVenc);
            parcelas.add(p);
            dataVenc = dataVenc.plusMonths(1);
        }
    }

    //@ ensures \result >= valorTotal;
    //@ pure helper
    private double calcularMontanteComJuros() {
        double taxaDecimal = taxaJuros / 100;
        return valorTotal * Math.pow(1 + taxaDecimal, numeroParcelas / 12.0);
    }

    //@ public normal_behavior
    //@   requires 1 <= numeroParcela && numeroParcela <= numeroParcelas;
    //@   requires conta != null;
    //@   requires !parcelas.get(numeroParcela - 1).isPaga();
    //@   requires conta.getSaldo() >= parcelas.get(numeroParcela - 1).getValorTotal();
    //@   assignable conta.saldo, parcelas.get(numeroParcela - 1).paga, parcelas.get(numeroParcela - 1).dataPagamento;
    //@   ensures parcelas.get(numeroParcela - 1).isPaga();
    //@ also
    //@ public exceptional_behavior
    //@   requires numeroParcela < 1 || numeroParcela > numeroParcelas ||
    //@            parcelas.get(numeroParcela - 1).isPaga() ||
    //@            conta.getSaldo() < parcelas.get(numeroParcela - 1).getValorTotal();
    //@   assignable \nothing;
    //@   signals_only SaldoInsuficienteException, ValidacaoException;
    public void pagarParcela(int numeroParcela, Conta conta)
            throws SaldoInsuficienteException, ValidacaoException {

        if (numeroParcela < 1 || numeroParcela > numeroParcelas) {
            throw new ValidacaoException("Número de parcela inválido.");
        }

        Parcela parcela = parcelas.get(numeroParcela - 1);

        if (parcela.isPaga()) {
            throw new ValidacaoException("Parcela já foi paga.");
        }

        double valorTotal = parcela.getValorTotal();

        conta.sacar(valorTotal);

        parcela.marcarComoPaga();
    }

    //@ ensures num < 1 || num > numeroParcelas ==> \result == false;
    //@ ensures 1 <= num && num <= numeroParcelas ==> \result == parcelas.get(num - 1).isPaga();
    //@ pure
    public boolean parcelaFoiPaga(int num) {
        if (num < 1 || num > numeroParcelas) {
            return false;
        }
        return parcelas.get(num - 1).isPaga();
    }

    //@ ensures num < 1 || num > numeroParcelas ==> \result == 0;
    //@ ensures 1 <= num && num <= numeroParcelas ==> \result == parcelas.get(num - 1).getValorTotal();
    //@ pure
    public double getValorParcela(int num) {
        if (num < 1 || num > numeroParcelas) {
            return 0;
        }
        return parcelas.get(num - 1).getValorTotal();
    }

    //@ ensures \result >= 0;
    //@ ensures \result <= numeroParcelas;
    //@ pure helper
    private /*@ spec_public @*/ int contarParcelasPagas() {
        int count = 0;
        //@ maintaining 0 <= i && i <= parcelas.size();
        //@ maintaining count >= 0 && count <= i;
        //@ loop_writes i, count;
        //@ decreases parcelas.size() - i;
        for (int i = 0; i < parcelas.size(); i++) {
            if (parcelas.get(i).isPaga()) {
                count++;
            }
        }
        return count;
    }

    //@ ensures \result >= 0;
    //@ pure helper
    private /*@ spec_public @*/ double calcularSaldoDevedor() {
        double total = 0;
        //@ maintaining 0 <= i && i <= parcelas.size();
        //@ maintaining total >= 0;
        //@ loop_writes i, total;
        //@ decreases parcelas.size() - i;
        for (int i = 0; i < parcelas.size(); i++) {
            if (!parcelas.get(i).isPaga()) {
                total += parcelas.get(i).getValor();
            }
        }
        return total;
    }

    //@ ensures \result == valorTotal;
    //@ ensures \result > 0;
    //@ pure
    public double getValorTotal() {
        return valorTotal;
    }

    //@ ensures \result == taxaJuros;
    //@ ensures \result >= 0;
    //@ pure
    public double getTaxaJuros() {
        return taxaJuros;
    }

    //@ ensures \result == numeroParcelas;
    //@ ensures \result > 0;
    //@ pure
    public int getNumeroParcelas() {
        return numeroParcelas;
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == numeroParcelas;
    //@ ensures \fresh(\result);
    //@ pure
    public List<Parcela> getParcelas() {
        return new ArrayList<>(parcelas);
    }

    //@ ensures \result == cliente;
    //@ ensures \result != null;
    //@ pure
    public Cliente getCliente() {
        return cliente;
    }

    //@ ensures \result == dataContratacao;
    //@ ensures \result != null;
    //@ pure
    public LocalDate getDataContratacao() {
        return dataContratacao;
    }

    //@ ensures \result >= 0;
    //@ ensures \result == calcularSaldoDevedor();
    //@ pure
    public double getSaldoDevedor() {
        return calcularSaldoDevedor();
    }

    //@ ensures \result >= 0;
    //@ ensures \result <= numeroParcelas;
    //@ ensures \result == contarParcelasPagas();
    //@ pure
    public int getParcelasPagas() {
        return contarParcelasPagas();
    }

    //@ ensures \result == (getParcelasPagas() == numeroParcelas);
    //@ pure
    public boolean isQuitado() {
        return getParcelasPagas() == numeroParcelas;
    }
}
