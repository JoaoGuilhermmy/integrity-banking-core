public class ContaPoupanca extends Conta {

    private /*@ spec_public @*/ double taxaRendimento;

    //@ public invariant taxaRendimento > 0;

    //@ requires numero >= 1000 && numero <= 9999;
    //@ requires titular != null;
    //@ requires taxa > 0;
    //@ ensures this.taxaRendimento == taxa;
    //@ pure
    public ContaPoupanca(int numero, double saldo, Cliente titular, double taxa) {
        super(numero, saldo, titular);
        this.taxaRendimento = taxa;
    }

    //@ ensures \result == taxaRendimento;
    //@ ensures \result > 0;
    //@ pure
    public double getTaxaRendimento() {
        return taxaRendimento;
    }

    //@ requires taxa > 0;
    //@ assignable taxaRendimento;
    //@ ensures taxaRendimento == taxa;
    public void setTaxaRendimento(double taxa) {
        this.taxaRendimento = taxa;
    }

    //@ public normal_behavior
    //@   requires taxaRendimento > 0;
    //@   assignable saldo, historicoTransacoes, getTitular().historicoTransacoes;
    //@   ensures getSaldo() > \old(getSaldo());
    //@   ensures getSaldo() == \old(getSaldo()) * (1 + taxaRendimento / 100);
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires taxaRendimento <= 0;
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public void renderJuros() throws ValidacaoException {
        if (this.taxaRendimento <= 0) {
            throw new ValidacaoException("Taxa de rendimento deve ser positiva para aplicar.");
        }

        double rendimento = this.getSaldo() * (this.taxaRendimento / 100);
        this.setSaldo(this.getSaldo() + rendimento);

        Transacao t = new Transacao(
                TipoTransacao.RENDIMENTO_POUPANCA,
                rendimento,
                "Rendimento de poupança (" + taxaRendimento + "%)",
                null,
                this
        );

        registrarTransacao(t);
    }

    //@ also
    //@ public normal_behavior
    //@   requires valor > 0;
    //@   requires valor <= getSaldo();
    //@   assignable saldo, historicoTransacoes, getTitular().historicoTransacoes;
    //@   ensures getSaldo() == \old(getSaldo()) - valor;
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires valor <= 0 || valor > getSaldo();
    //@   assignable \nothing;
    //@   signals_only SaldoInsuficienteException, ValidacaoException;
    public void sacar(double valor) throws SaldoInsuficienteException, ValidacaoException {
        if (valor <= 0) {
            throw new ValidacaoException("O valor do saque deve ser positivo.");
        }

        if (valor > this.getSaldo()) {
            throw new SaldoInsuficienteException(
                    "Saldo insuficiente para este saque. Disponível: R$ " + this.getSaldo()
            );
        }

        this.setSaldo(this.getSaldo() - valor);

        Transacao t = new Transacao(
                TipoTransacao.SAQUE,
                valor,
                "Saque em conta poupança " + this.getNumero(),
                this,
                null
        );

        registrarTransacao(t);
    }

    //@ also
    //@ ensures \result == 0.0;
    //@ pure
    public double calcularTarifa() {
        return 0.0;
    }
}
