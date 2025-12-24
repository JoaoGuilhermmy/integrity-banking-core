import java.util.ArrayList;
import java.util.List;

public class Cliente extends Pessoa {
    private /*@ spec_public @*/ static int contador = 0;

    private /*@ spec_public @*/ int id;
    private /*@ spec_public @*/ String tipoCliente;
    private /*@ spec_public @*/ double renda;

    private /*@ spec_public @*/ List<Conta> contas;
    private /*@ spec_public @*/ List<Transacao> historicoTransacoes;
    private /*@ spec_public @*/ List<Emprestimo> emprestimos;

    //@ public invariant id > 0;
    //@ public invariant tipoCliente != null && !tipoCliente.isEmpty();
    //@ public invariant renda >= 0;
    //@ public invariant contas != null;
    //@ public invariant historicoTransacoes != null;
    //@ public invariant emprestimos != null;
    //@ public invariant (\forall int i; 0 <= i && i < contas.size(); contas.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < historicoTransacoes.size(); historicoTransacoes.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < emprestimos.size(); emprestimos.get(i) != null);

    //@ requires nome != null && !nome.isEmpty();
    //@ requires cpf != null && cpf.length() == 11;
    //@ requires endereco != null;
    //@ requires telefone != null && telefone.length() >= 8 && telefone.length() <= 13;
    //@ requires tipo != null && !tipo.isEmpty();
    //@ requires r >= 0;
    //@ ensures this.id > \old(contador);
    //@ ensures this.tipoCliente.equals(tipo);
    //@ ensures this.renda == r;
    //@ ensures this.contas != null && this.contas.size() == 0;
    //@ ensures this.historicoTransacoes != null && this.historicoTransacoes.size() == 0;
    //@ ensures this.emprestimos != null && this.emprestimos.size() == 0;
    //@ pure
    public Cliente(String nome, String cpf, String endereco, String telefone,
                   String tipo, double r) {
        super(nome, cpf, endereco, telefone);
        contador++;
        this.id = contador;
        this.tipoCliente = tipo;
        this.renda = r;
        this.contas = new ArrayList<>();
        this.historicoTransacoes = new ArrayList<>();
        this.emprestimos = new ArrayList<>();
    }

    //@ ensures \result == id;
    //@ ensures \result > 0;
    //@ pure
    public int getId() {
        return id;
    }

    //@ ensures \result == tipoCliente;
    //@ ensures \result != null && !\result.isEmpty();
    //@ pure
    public String getTipoCliente() {
        return tipoCliente;
    }

    //@ requires tipo != null && !tipo.isEmpty();
    //@ assignable tipoCliente;
    //@ ensures tipoCliente.equals(tipo);
    public void setTipoCliente(String tipo) {
        this.tipoCliente = tipo;
    }

    public /*@ pure @*/ String getNome() {
        return super.getNome();
    }

    //@ ensures \result == renda;
    //@ ensures \result >= 0;
    //@ pure
    public double getRenda() {
        return renda;
    }

    //@ requires r >= 0;
    //@ assignable renda;
    //@ ensures renda == r;
    public void setRenda(double r) {
        this.renda = r;
    }

    //@ also
    //@ ensures \result != null;
    //@ ensures \result.contains(String.valueOf(id));
    // @ ensures \result.contains(getNome());
    //@ ensures this.getNome() != null;
    //@ pure
    public String getDescricao() {
        return "Cliente nº " + this.id + " - " + this.getNome();
    }

    //@ requires conta != null;
    //@ requires !contas.contains(conta);
    //@ assignable contas;
    //@ ensures contas.contains(conta);
    //@ ensures contas.size() == \old(contas.size()) + 1;
    public void adicionarConta(Conta conta) {
        if (conta != null && !contas.contains(conta)) {
            this.contas.add(conta);
        }
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == contas.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<Conta> getContas() {
        return new ArrayList<>(this.contas);
    }

    //@ requires transacao != null;
    //@ assignable historicoTransacoes;
    //@ ensures historicoTransacoes.contains(transacao);
    //@ ensures historicoTransacoes.size() == \old(historicoTransacoes.size()) + 1;
    public void registrarTransacao(Transacao transacao) {
        if (transacao != null) {
            this.historicoTransacoes.add(transacao);
        }
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == historicoTransacoes.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<Transacao> getHistoricoTransacoes() {
        return new ArrayList<>(this.historicoTransacoes);
    }

    //@ requires emprestimo != null;
    //@ assignable emprestimos;
    //@ ensures emprestimos.contains(emprestimo);
    //@ ensures emprestimos.size() == \old(emprestimos.size()) + 1;
    public void adicionarEmprestimo(Emprestimo emprestimo) {
        if (emprestimo != null) {
            this.emprestimos.add(emprestimo);
        }
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == emprestimos.size();
    //@ ensures \fresh(\result);
    //@ pure
    public List<Emprestimo> getEmprestimos() {
        return new ArrayList<>(this.emprestimos);
    }

    //@ ensures \result >= 0;
    //@ pure helper
    private /*@ spec_public @*/ double calcularLimiteCredito() {
        double multiplicador = tipoCliente.equals("premium") ? 5.0 : 3.0;

        double totalEmprestimosAtivos = 0;
        //@ maintaining 0 <= i && i <= emprestimos.size();
        //@ maintaining totalEmprestimosAtivos >= 0;
        //@ loop_writes i, totalEmprestimosAtivos;
        //@ decreases emprestimos.size() - i;
        for (int i = 0; i < emprestimos.size(); i++) {
            Emprestimo emp = emprestimos.get(i);
            if (!emp.isQuitado()) {
                totalEmprestimosAtivos += emp.getSaldoDevedor();
            }
        }

        double limiteBase = renda * multiplicador;
        double limiteDisponivel = limiteBase - totalEmprestimosAtivos;

        return Math.max(0, limiteDisponivel);
    }

    //@ ensures \result >= 0;
    //@ ensures \result == calcularLimiteCredito();
    //@ pure
    public double getLimiteCredito() {
        return calcularLimiteCredito();
    }

    //@ ensures \result == true;
    //@ pure
    public boolean emConformidade() {
        return true;
    }

    //@ ensures \result >= 0;
    //@ pure
    public double calcularSaldoTotal() {
        double total = 0;
        //@ maintaining 0 <= i && i <= contas.size();
        //@ maintaining total >= 0;
        //@ loop_writes i, total;
        //@ decreases contas.size() - i;
        for (int i = 0; i < contas.size(); i++) {
            total += contas.get(i).getSaldo();
        }
        return total;
    }
}
