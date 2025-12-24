import java.util.ArrayList;
import java.util.List;

public class ContaInvestimento extends Conta {

    private /*@ spec_public @*/ List<Investimento> carteira;

    //@ public invariant carteira != null;
    //@ public invariant (\forall int i; 0 <= i && i < carteira.size(); carteira.get(i) != null);

    //@ requires numero >= 1000 && numero <= 9999;
    //@ requires titular != null;
    //@ ensures this.carteira != null;
    //@ ensures this.carteira.size() == 0;
    //@ pure
    public ContaInvestimento(int numero, double saldo, Cliente titular) {
        super(numero, saldo, titular);
        this.carteira = new ArrayList<>();
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == carteira.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<Investimento> getCarteira() {
        return new ArrayList<>(this.carteira);
    }

    //@ ensures \result >= 0;
    //@ pure helper
    private /*@ spec_public @*/ double calcularValorTotalInvestido() {
        double total = 0;
        //@ maintaining 0 <= i && i <= carteira.size();
        //@ maintaining total >= 0;
        //@ loop_writes i, total;
        //@ decreases carteira.size() - i;
        for (int i = 0; i < carteira.size(); i++) {
            Investimento inv = carteira.get(i);
            if (!inv.isResgatado()) {
                total += inv.getValorInicial();
            }
        }
        return total;
    }

    //@ ensures \result >= 0;
    //@ pure helper
    private /*@ spec_public @*/ double calcularValorTotalAtual() {
        double total = 0;
        //@ maintaining 0 <= i && i <= carteira.size();
        //@ maintaining total >= 0;
        //@ loop_writes i, total;
        //@ decreases carteira.size() - i;
        for (int i = 0; i < carteira.size(); i++) {
            Investimento inv = carteira.get(i);
            if (!inv.isResgatado()) {
                total += inv.getValorAtual();
            }
        }
        return total;
    }

    //@ ensures \result >= 0;
    //@ ensures \result == calcularValorTotalInvestido();
    //@ pure
    public double getValorTotalInvestido() {
        return calcularValorTotalInvestido();
    }

    //@ ensures \result >= 0;
    //@ ensures \result == calcularValorTotalAtual();
    //@ pure
    public double getValorTotalAtual() {
        return calcularValorTotalAtual();
    }

    //@ ensures \result == getValorTotalAtual() - getValorTotalInvestido();
    //@ pure
    public double getRendimentoTotal() {
        return getValorTotalAtual() - getValorTotalInvestido();
    }

    //@ public normal_behavior
    //@   requires tipo != null;
    //@   requires montante > 0;
    //@   requires montante <= getSaldo();
    //@   assignable saldo, carteira, historicoTransacoes, getTitular().historicoTransacoes;
    //@   ensures getSaldo() == \old(getSaldo()) - montante;
    //@   ensures carteira.size() == \old(carteira.size()) + 1;
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires tipo == null || montante <= 0 || montante > getSaldo();
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public void investir(TipoInvestimento tipo, double montante) throws ValidacaoException {
        if (montante <= 0) {
            throw new ValidacaoException("Montante deve ser positivo.");
        }

        if (montante > getSaldo()) {
            throw new ValidacaoException(
                    "Saldo insuficiente. Disponível: R$ " + getSaldo()
            );
        }

        Investimento inv = new Investimento(tipo, montante);
        carteira.add(inv);

        this.setSaldo(this.getSaldo() - montante);

        Transacao t = new Transacao(
                TipoTransacao.APLICACAO_INVESTIMENTO,
                montante,
                "Investimento em " + tipo,
                this,
                null
        );

        registrarTransacao(t);
    }

    //@ public normal_behavior
    //@   requires 0 <= indice && indice < carteira.size();
    //@   requires !carteira.get(indice).isResgatado();
    //@   requires carteira.get(indice).podeResgatar();
    //@   assignable saldo, carteira.get(indice).resgatado, carteira.get(indice).dataResgate, historicoTransacoes, getTitular().historicoTransacoes;
    //@   ensures getSaldo() > \old(getSaldo());
    //@   ensures carteira.get(indice).isResgatado();
    //@   ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires indice < 0 || indice >= carteira.size() ||
    //@            carteira.get(indice).isResgatado() ||
    //@            !carteira.get(indice).podeResgatar();
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public void resgatar(int indice) throws ValidacaoException {
        if (indice < 0 || indice >= carteira.size()) {
            throw new ValidacaoException("Índice de investimento inválido.");
        }

        Investimento inv = carteira.get(indice);

        if (inv.isResgatado()) {
            throw new ValidacaoException("Investimento já foi resgatado.");
        }

        double valorResgate = inv.resgatar();

        this.setSaldo(this.getSaldo() + valorResgate);

        Transacao t = new Transacao(
                TipoTransacao.RESGATE_INVESTIMENTO,
                valorResgate,
                "Resgate de investimento " + inv.getTipo(),
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
                    "Saldo insuficiente. Disponível: R$ " + this.getSaldo()
            );
        }

        this.setSaldo(this.getSaldo() - valor);

        Transacao t = new Transacao(
                TipoTransacao.SAQUE,
                valor,
                "Saque em conta investimento " + this.getNumero(),
                this,
                null
        );

        registrarTransacao(t);
    }

    //@ also
    //@ ensures getTitular().getTipoCliente().equals("premium") ==> \result == 0.0;
    //@ ensures !getTitular().getTipoCliente().equals("premium") ==> \result == 20.0;
    //@ ensures \result >= 0;
    //@ pure
    public double calcularTarifa() {
        return getTitular().getTipoCliente().equals("premium") ? 0.0 : 20.0;
    }
}
