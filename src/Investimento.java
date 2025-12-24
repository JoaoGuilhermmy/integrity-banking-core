import java.time.LocalDate;
import java.time.temporal.ChronoUnit;

public class Investimento {

    private /*@ spec_public @*/ TipoInvestimento tipo;
    private /*@ spec_public @*/ double valorInicial;
    private /*@ spec_public @*/ LocalDate dataAplicacao;
    private /*@ spec_public @*/ boolean resgatado;
    private /*@ spec_public @*/ /*@ nullable @*/ LocalDate dataResgate;

    //@ public invariant tipo != null;
    //@ public invariant valorInicial > 0;
    //@ public invariant dataAplicacao != null;
    //@ public invariant resgatado ==> dataResgate != null;
    //@ public invariant !resgatado ==> dataResgate == null;
    //@ public invariant resgatado ==> !dataResgate.isBefore(dataAplicacao);

    //@ requires t != null;
    //@ requires valor > 0;
    //@ ensures this.tipo == t;
    //@ ensures this.valorInicial == valor;
    //@ ensures this.dataAplicacao != null;
    //@ ensures !this.resgatado;
    //@ ensures this.dataResgate == null;
    //@ pure
    public Investimento(TipoInvestimento t, double valor) {
        this.tipo = t;
        this.valorInicial = valor;
        this.dataAplicacao = LocalDate.now();
        this.resgatado = false;
        this.dataResgate = null;
    }

    //@ ensures \result == tipo;
    //@ ensures \result != null;
    //@ pure
    public TipoInvestimento getTipo() {
        return tipo;
    }

    //@ ensures \result == valorInicial;
    //@ ensures \result > 0;
    //@ pure
    public double getValorInicial() {
        return valorInicial;
    }

    //@ ensures \result == dataAplicacao;
    //@ ensures \result != null;
    //@ pure
    public LocalDate getDataAplicacao() {
        return dataAplicacao;
    }

    //@ ensures \result == resgatado;
    //@ pure
    public boolean isResgatado() {
        return resgatado;
    }

    //@ ensures \result == dataResgate;
    //@ ensures resgatado ==> \result != null;
    //@ ensures !resgatado ==> \result == null;
    //@ pure
    public /*@ nullable @*/ LocalDate getDataResgate() {
        return dataResgate;
    }

    //@ ensures \result >= 0;
    //@ pure helper
    private /*@ spec_public @*/ long calcularDiasInvestidos() {
        LocalDate dataFim = resgatado ? dataResgate : LocalDate.now();
        return ChronoUnit.DAYS.between(dataAplicacao, dataFim);
    }

    //@ ensures \result >= 0;
    //@ ensures \result == calcularDiasInvestidos();
    //@ pure
    public long getDiasInvestidos() {
        return calcularDiasInvestidos();
    }

    //@ ensures \result >= valorInicial;
    //@ pure helper
    private /*@ spec_public @*/ double calcularValorAtual() {
        long dias = resgatado
                ? ChronoUnit.DAYS.between(dataAplicacao, dataResgate)
                : ChronoUnit.DAYS.between(dataAplicacao, LocalDate.now());

        double meses = dias / 30.0;
        double taxaDecimal = tipo.getTaxaMensal() / 100.0;

        return valorInicial * Math.pow(1 + taxaDecimal, meses);
    }

    //@ ensures \result >= valorInicial;
    //@ ensures \result == calcularValorAtual();
    //@ pure
    public double getValorAtual() {
        return calcularValorAtual();
    }

    //@ ensures \result >= 0;
    //@ ensures \result == getValorAtual() - valorInicial;
    //@ pure
    public double getRendimento() {
        return getValorAtual() - valorInicial;
    }

    //@ ensures \result == (!resgatado && getDiasInvestidos() >= tipo.getDiasCarencia());
    //@ pure
    public boolean podeResgatar() {
        return !resgatado && getDiasInvestidos() >= tipo.getDiasCarencia();
    }

    //@ public normal_behavior
    //@   requires !resgatado;
    //@   requires getDiasInvestidos() >= tipo.getDiasCarencia();
    //@   assignable resgatado, dataResgate;
    //@   ensures resgatado;
    //@   ensures dataResgate != null;
    //@   ensures \result >= valorInicial;
    //@ also
    //@ public exceptional_behavior
    //@   requires resgatado || getDiasInvestidos() < tipo.getDiasCarencia();
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public double resgatar() throws ValidacaoException {
        if (resgatado) {
            throw new ValidacaoException("Investimento já foi resgatado.");
        }

        if (!podeResgatar()) {
            throw new ValidacaoException(
                    "Período de carência não cumprido. Necessário " +
                            tipo.getDiasCarencia() + " dias, investido apenas " +
                            getDiasInvestidos() + " dias."
            );
        }

        this.resgatado = true;
        this.dataResgate = LocalDate.now();

        return getValorAtual();
    }

    //@ ensures \result != null;
    //@ pure
    public String getResumo() {
        return String.format(
                "%s - Valor Inicial: R$ %.2f | Valor Atual: R$ %.2f | Rendimento: R$ %.2f | Dias: %d | Status: %s",
                tipo, valorInicial, getValorAtual(), getRendimento(),
                getDiasInvestidos(), resgatado ? "RESGATADO" : "ATIVO"
        );
    }
}
