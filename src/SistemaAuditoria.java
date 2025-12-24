import java.util.ArrayList;
import java.util.List;

public class SistemaAuditoria {

    private /*@ spec_public @*/ List<Transacao> transacoesAuditadas;
    private /*@ spec_public @*/ List<String> alertas;

    //@ public invariant transacoesAuditadas != null;
    //@ public invariant alertas != null;
    //@ public invariant (\forall int i; 0 <= i && i < transacoesAuditadas.size(); transacoesAuditadas.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < alertas.size(); alertas.get(i) != null);

    //@ ensures transacoesAuditadas != null;
    //@ ensures transacoesAuditadas.size() == 0;
    //@ ensures alertas != null;
    //@ ensures alertas.size() == 0;
    //@ pure
    public SistemaAuditoria() {
        this.transacoesAuditadas = new ArrayList<>();
        this.alertas = new ArrayList<>();
    }

    //@ requires transacao != null;
    //@ assignable transacoesAuditadas, alertas;
    //@ ensures transacoesAuditadas.size() == \old(transacoesAuditadas.size()) + 1;
    //@ ensures transacoesAuditadas.contains(transacao);
    //@ ensures transacao.requerDocumentacao() ==> alertas.size() > \old(alertas.size());
    //@ ensures transacao.getValor() >= 50000 ==> alertas.size() > \old(alertas.size());
    public void auditarTransacao(Transacao transacao) {
        transacoesAuditadas.add(transacao);

        if (transacao.requerDocumentacao()) {
            String alerta = String.format(
                    "ALERTA: Transação %d de valor R$ %.2f requer documentação",
                    transacao.getId(), transacao.getValor()
            );
            alertas.add(alerta);
        }

        if (transacao.getValor() >= 50000) {
            String alerta = String.format(
                    "ALERTA CRÍTICO: Transação %d de alto valor: R$ %.2f",
                    transacao.getId(), transacao.getValor()
            );
            alertas.add(alerta);
        }
    }

    //@ requires cliente != null;
    //@ ensures \result ==> (\forall int i; 0 <= i && i < cliente.getHistoricoTransacoes().size();
    //@                      !cliente.getHistoricoTransacoes().get(i).requerDocumentacao() ||
    //@                      verificarTransacaoAuditada(cliente.getHistoricoTransacoes().get(i)));
    //@ pure
    public boolean clienteEmConformidade(Cliente cliente) {
        List<Transacao> transacoes = cliente.getHistoricoTransacoes();

        //@ maintaining 0 <= i && i <= transacoes.size();
        //@ maintaining (\forall int j; 0 <= j && j < i;
        //@              !transacoes.get(j).requerDocumentacao() ||
        //@              verificarTransacaoAuditada(transacoes.get(j)));
        //@ loop_writes i;
        //@ decreases transacoes.size() - i;
        for (int i = 0; i < transacoes.size(); i++) {
            Transacao t = transacoes.get(i);
            if (t.requerDocumentacao() && !verificarTransacaoAuditada(t)) {
                return false;
            }
        }

        return true;
    }

    //@ requires transacao != null;
    //@ ensures \result == transacoesAuditadas.contains(transacao);
    //@ pure helper
    private /*@ spec_public @*/ boolean verificarTransacaoAuditada(Transacao transacao) {
        return transacoesAuditadas.contains(transacao);
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == transacoesAuditadas.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<Transacao> getTransacoesAuditadas() {
        return new ArrayList<>(transacoesAuditadas);
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == alertas.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<String> getAlertas() {
        return new ArrayList<>(alertas);
    }

    //@ ensures \result == transacoesAuditadas.size();
    //@ ensures \result >= 0;
    //@ pure
    public int getTotalOperacoesAuditadas() {
        return transacoesAuditadas.size();
    }

    //@ requires valor >= 0;
    //@ ensures \result >= 0;
    //@ ensures \result <= transacoesAuditadas.size();
    //@ pure
    public int contarTransacoesPorValorMinimo(double valor) {
        int count = 0;

        //@ maintaining 0 <= i && i <= transacoesAuditadas.size();
        //@ maintaining count >= 0 && count <= i;
        //@ loop_writes i, count;
        //@ decreases transacoesAuditadas.size() - i;
        for (int i = 0; i < transacoesAuditadas.size(); i++) {
            if (transacoesAuditadas.get(i).getValor() >= valor) {
                count++;
            }
        }

        return count;
    }

    //@ assignable alertas;
    //@ ensures alertas.size() == 0;
    public void limparAlertas() {
        alertas.clear();
    }
}
