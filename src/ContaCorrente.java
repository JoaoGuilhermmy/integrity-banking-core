public class ContaCorrente extends Conta {

    private /*@ spec_public @*/ double limiteChequeEspecial;
    private /*@ spec_public @*/ int diasEmDebito;

    //@ public invariant limiteChequeEspecial >= 0;
    //@ public invariant diasEmDebito >= 0;
    //@ public invariant saldo < 0 ==> diasEmDebito > 0;

    //@ requires numero >= 1000 && numero <= 9999;
    //@ requires titular != null;
    //@ requires limite >= 0;
    //@ ensures this.limiteChequeEspecial == limite;
    //@ ensures this.diasEmDebito == 0;
    //@ pure
    public ContaCorrente(int numero, double saldo, Cliente titular, double limite) {
        super(numero, saldo, titular);
        this.limiteChequeEspecial = limite;
        this.diasEmDebito = 0;
    }

    //@ ensures \result == limiteChequeEspecial;
    //@ ensures \result >= 0;
    //@ pure
    public double getLimiteChequeEspecial() {
        return limiteChequeEspecial;
    }

    //@ requires limite >= 0;
    //@ assignable limiteChequeEspecial;
    //@ ensures limiteChequeEspecial == limite;
    public void setLimiteChequeEspecial(double limite) {
        this.limiteChequeEspecial = limite;
    }

    //@ ensures \result == diasEmDebito;
    //@ ensures \result >= 0;
    //@ pure
    public int getDiasEmDebito() {
        return diasEmDebito;
    }

    //@ requires dias >= 0;
    //@ ensures \result >= 0;
    //@ pure
    public double calcularJurosDebito(int dias) {
        return Math.abs(getSaldo()) * (0.01 * dias);
    }

    //@ also
    //@ public normal_behavior
    //@   requires valor > 0;
    //@   requires valor <= getSaldo() + limiteChequeEspecial;
    //@   assignable saldo, diasEmDebito, historicoTransacoes, getTitular().historicoTransacoes;
    //@   ensures getSaldo() == \old(getSaldo()) - valor;
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires valor <= 0 || valor > getSaldo() + limiteChequeEspecial;
    //@   assignable \nothing;
    //@   signals_only SaldoInsuficienteException, ValidacaoException;
    public void sacar(double valor) throws SaldoInsuficienteException, ValidacaoException {
        if (valor <= 0) {
            throw new ValidacaoException("O valor do saque deve ser positivo.");
        }

        double saldoDisp = this.getSaldo() + this.limiteChequeEspecial;

        if (valor > saldoDisp) {
            throw new SaldoInsuficienteException(
                    "Saldo e limite insuficientes para este saque. Disponível: R$ " + saldoDisp
            );
        }

        this.setSaldo(this.getSaldo() - valor);

        if (this.getSaldo() < 0) {
            diasEmDebito++;
        }

        Transacao t = new Transacao(
                TipoTransacao.SAQUE,
                valor,
                "Saque em conta " + this.getNumero(),
                this,
                null
        );

        registrarTransacao(t);
    }

    //@ also
    //@ ensures getTitular().getTipoCliente().equals("premium") ==> \result == 0.0;
    //@ ensures !getTitular().getTipoCliente().equals("premium") ==> \result == 15.0;
    //@ ensures \result >= 0;
    //@ pure
    public double calcularTarifa() {
        return getTitular().getTipoCliente().equals("premium") ? 0.0 : 15.0;
    }
}
