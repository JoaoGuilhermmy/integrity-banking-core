import java.util.ArrayList;
import java.util.List;

public abstract class Conta {

    private /*@ spec_public @*/ int numero;
    private /*@ spec_public @*/ double saldo;
    private /*@ spec_public @*/ Cliente titular;
    private /*@ spec_public @*/ List<Transacao> historicoTransacoes;

    //@ public invariant numero >= 1000 && numero <= 9999;
    //@ public invariant titular != null;
    //@ public invariant historicoTransacoes != null;
    //@ public invariant (\forall int i; 0 <= i && i < historicoTransacoes.size(); historicoTransacoes.get(i) != null);

    //@ requires num >= 1000 && num <= 9999;
    //@ requires tit != null;
    //@ ensures this.numero == num;
    //@ ensures this.saldo == s;
    //@ ensures this.titular == tit;
    //@ ensures this.historicoTransacoes != null;
    //@ ensures this.historicoTransacoes.size() == 0;
    //@ pure
    public Conta(int num, double s, Cliente tit) {
        this.numero = num;
        this.titular = tit;
        this.saldo = s;
        this.historicoTransacoes = new ArrayList<>();
    }

    //@ ensures \result == this.numero;
    //@ ensures \result >= 1000 && \result <= 9999;
    //@ pure
    public int getNumero() {
        return this.numero;
    }

    //@ requires num >= 1000 && num <= 9999;
    //@ assignable numero;
    //@ ensures this.numero == num;
    public void setNumero(int num) {
        this.numero = num;
    }

    //@ ensures \result == this.saldo;
    //@ pure
    public double getSaldo() {
        return this.saldo;
    }

    //@ assignable saldo;
    //@ ensures this.saldo == s;
    protected void setSaldo(double s) {
        this.saldo = s;
    }

    //@ ensures \result == this.titular;
    //@ ensures \result != null;
    //@ pure
    public Cliente getTitular() {
        return this.titular;
    }

    //@ requires tit != null;
    //@ assignable titular;
    //@ ensures this.titular == tit;
    public void setTitular(Cliente tit) {
        this.titular = tit;
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == historicoTransacoes.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<Transacao> getHistoricoTransacoes() {
        return new ArrayList<>(this.historicoTransacoes);
    }

    //@ requires transacao != null;
    //@ assignable historicoTransacoes, titular.historicoTransacoes;
    //@ ensures historicoTransacoes.contains(transacao);
    //@ ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    protected void registrarTransacao(Transacao transacao) {
        this.historicoTransacoes.add(transacao);
        this.titular.registrarTransacao(transacao);
    }

    //@ public normal_behavior
    //@   requires valor > 0;
    //@   assignable saldo, historicoTransacoes, titular.historicoTransacoes;
    //@   ensures saldo == \old(saldo) + valor;
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires valor <= 0;
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public void depositar(double valor) throws ValidacaoException {
        if (valor <= 0) {
            throw new ValidacaoException("O valor do depósito deve ser positivo.");
        }

        this.saldo += valor;

        Transacao t = new Transacao(
                TipoTransacao.DEPOSITO,
                valor,
                "Depósito em conta " + this.numero,
                null,
                this
        );

        registrarTransacao(t);
    }

    //@ requires valor > 0;
    //@ assignable saldo, historicoTransacoes, titular.historicoTransacoes;
    //@ signals_only SaldoInsuficienteException, ValidacaoException;
    public abstract void sacar(double valor)
            throws SaldoInsuficienteException, ValidacaoException;

    //@ ensures \result >= 0;
    //@ pure
    public abstract double calcularTarifa();

    //@ public normal_behavior
    //@   requires saldo >= calcularTarifa();
    //@   assignable saldo, historicoTransacoes, titular.historicoTransacoes;
    //@   ensures saldo == \old(saldo) - calcularTarifa();
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires saldo < calcularTarifa();
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public void cobrarTarifa() throws ValidacaoException {
        double tarifa = calcularTarifa();

        if (tarifa > saldo) {
            throw new ValidacaoException("Saldo insuficiente para cobrança de tarifa.");
        }

        this.saldo -= tarifa;

        Transacao t = new Transacao(
                TipoTransacao.COBRANCA_TARIFA,
                tarifa,
                "Tarifa mensal",
                this,
                null
        );

        registrarTransacao(t);
    }
}
