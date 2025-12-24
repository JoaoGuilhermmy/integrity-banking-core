import java.util.*;

public class BancoService {

    private /*@ spec_public @*/ List<Cliente> clientes;
    private /*@ spec_public @*/ List<Conta> contas;
    private /*@ spec_public @*/ List<Funcionario> funcionarios;
    private /*@ spec_public @*/ List<Emprestimo> emprestimos;

    private /*@ spec_public @*/ SistemaAuditoria auditoria;
    private /*@ spec_public @*/ HashSet<Integer> numerosUsados;
    private /*@ spec_public @*/ Random random;

    //@ public invariant clientes != null;
    //@ public invariant contas != null;
    //@ public invariant funcionarios != null;
    //@ public invariant emprestimos != null;
    //@ public invariant auditoria != null;
    //@ public invariant numerosUsados != null;
    //@ public invariant random != null;
    //@ public invariant (\forall int i; 0 <= i && i < clientes.size(); clientes.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < contas.size(); contas.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < funcionarios.size(); funcionarios.get(i) != null);
    //@ public invariant (\forall int i; 0 <= i && i < emprestimos.size(); emprestimos.get(i) != null);

    //@ ensures clientes != null && clientes.isEmpty();
    //@ ensures contas != null && contas.isEmpty();
    //@ ensures funcionarios != null && funcionarios.isEmpty();
    //@ ensures emprestimos != null && emprestimos.isEmpty();
    //@ ensures auditoria != null;
    //@ ensures numerosUsados != null && numerosUsados.isEmpty();
    //@ ensures random != null;
    public BancoService() {
        this.clientes = new ArrayList<>();
        this.contas = new ArrayList<>();
        this.funcionarios = new ArrayList<>();
        this.emprestimos = new ArrayList<>();
        this.auditoria = new SistemaAuditoria();
        this.numerosUsados = new HashSet<>();
        this.random = new Random();
    }

    //@ ensures \result >= 1000 && \result <= 9999;
    //@ assignable numerosUsados;
    private int gerarNumeroContaUnico() {
        int numero;
        do {
            numero = random.nextInt(9000) + 1000;
        } while (numerosUsados.contains(numero));
        numerosUsados.add(numero);
        return numero;
    }

    // ========================= CLIENTES =========================

    //@ public normal_behavior
    //@   requires nome != null && !nome.isEmpty();
    //@   requires cpf != null && cpf.length() == 11;
    //@   requires !existeCliente(cpf);
    //@   assignable clientes;
    //@   ensures clientes.size() == \old(clientes.size()) + 1;
    //@   ensures \result != null;
    //@   ensures \result.getCpf().equals(cpf);
    //@   ensures clientes.contains(\result);
    //@ also
    //@ public exceptional_behavior
    //@   requires existeCliente(cpf);
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public Cliente cadastrarCliente(String nome, String cpf, String endereco,
                                    String telefone, String tipoCliente, double renda)
            throws ValidacaoException {

        if (existeCliente(cpf)) {
            throw new ValidacaoException("CPF já cadastrado.");
        }

        Cliente cliente = new Cliente(nome, cpf, endereco, telefone, tipoCliente, renda);
        clientes.add(cliente);
        return cliente;
    }

    //@ public normal_behavior
    //@   requires cpf != null;
    //@   requires existeCliente(cpf);
    //@   ensures \result != null;
    //@   ensures \result.getCpf().equals(cpf);
    //@ also
    //@ public exceptional_behavior
    //@   requires !existeCliente(cpf);
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public /*@ pure @*/ Cliente buscarClientePorCpf(String cpf) throws ValidacaoException {
        for (Cliente c : clientes) {
            if (c.getCpf().equals(cpf)) {
                return c;
            }
        }
        throw new ValidacaoException("Cliente não encontrado.");
    }

    //@ requires cpf != null;
    //@ ensures \result == (\exists int i; 0 <= i && i < clientes.size(); clientes.get(i).getCpf().equals(cpf));
    private /*@ spec_public pure helper @*/ boolean existeCliente(String cpf) {
        for (Cliente c : clientes) {
            if (c.getCpf().equals(cpf)) {
                return true;
            }
        }
        return false;
    }

    //@ public normal_behavior
    //@   requires cpf != null;
    //@   requires existeCliente(cpf);
    //@   requires (\forall int i; 0 <= i && i < contas.size(); !contas.get(i).getTitular().getCpf().equals(cpf));
    //@   assignable clientes;
    //@   ensures clientes.size() == \old(clientes.size()) - 1;
    //@   ensures !existeCliente(cpf);
    //@ also
    //@ public exceptional_behavior
    //@   requires !existeCliente(cpf) || (\exists int i; 0 <= i && i < contas.size(); contas.get(i).getTitular().getCpf().equals(cpf));
    //@   assignable \nothing;
    //@   signals_only ValidacaoException;
    public void removerCliente(String cpf) throws ValidacaoException {
        Cliente cliente = buscarClientePorCpf(cpf);

        boolean temConta = false;
        for (Conta c : contas) {
            if (c.getTitular().getCpf().equals(cpf)) {
                temConta = true;
                break;
            }
        }

        if (temConta) {
            throw new ValidacaoException(
                    "Cliente não pode ser removido. Contas ativas encontradas. Remova as contas primeiro."
            );
        }

        clientes.remove(cliente);
    }

    //@ requires cpf != null;
    //@ ensures \result >= 0;
    private /*@ spec_public pure @*/ int contasPorCpf(String cpf) {
        int count = 0;
        for (Conta conta : contas) {
            if (conta.getTitular().getCpf().equals(cpf)) {
                count++;
            }
        }
        return count;
    }

    //@ requires cpf != null;
    //@ ensures existeCliente(cpf);
    public void atualizarDadosCliente(String cpf, String novoEndereco,
                                      String novoTelefone, String novoTipoCliente,
                                      double novaRenda) throws ValidacaoException {

        Cliente cliente = buscarClientePorCpf(cpf);

        if (novoEndereco != null && !novoEndereco.isEmpty())
            cliente.setEndereco(novoEndereco);

        if (novoTelefone != null && novoTelefone.length() >= 8 && novoTelefone.length() <= 13)
            cliente.setTelefone(novoTelefone);

        if (novoTipoCliente != null && !novoTipoCliente.isEmpty())
            cliente.setTipoCliente(novoTipoCliente);

        if (novaRenda >= 0)
            cliente.setRenda(novaRenda);
    }

    //@ ensures \result != null;
    //@ ensures \result.size() == clientes.size();
    //@ pure
    public List<Cliente> listarClientes() {
        return new ArrayList<>(clientes);
    }

    // ========================= FUNCIONÁRIOS =========================

    //@ public normal_behavior
    //@   requires cpf != null && nome != null;
    //@   requires !existeFuncionario(cpf, matricula);
    //@   assignable funcionarios;
    //@   ensures funcionarios.size() == \old(funcionarios.size()) + 1;
    //@   ensures \result != null;
    //@ also
    //@ public exceptional_behavior
    //@   requires existeFuncionario(cpf, matricula);
    //@   signals_only ValidacaoException;
    public Funcionario cadastrarFuncionario(String nome, String cpf, String endereco, String telefone,
                                            int matricula, String cargo, double salario) throws ValidacaoException {

        if (existeFuncionario(cpf, matricula)) {
            throw new ValidacaoException("CPF ou Matrícula já cadastrado.");
        }

        Funcionario funcionario = new Funcionario(nome, cpf, endereco, telefone, matricula, cargo, salario);
        funcionarios.add(funcionario);
        return funcionario;
    }

    //@ requires cpf != null;
    //@ ensures \result == (\exists int i; 0 <= i && i < funcionarios.size(); funcionarios.get(i).getCpf().equals(cpf) || funcionarios.get(i).getMatricula() == matricula);
    private /*@ spec_public pure helper @*/ boolean existeFuncionario(String cpf, int matricula) {
        for (Funcionario f : funcionarios) {
            if (f.getCpf().equals(cpf) || f.getMatricula() == matricula) {
                return true;
            }
        }
        return false;
    }

    //@ ensures \result != null;
    public /*@ pure @*/ Funcionario buscarFuncionarioPorCpf(String cpf) throws ValidacaoException {
        for (Funcionario f : funcionarios) {
            if (f.getCpf().equals(cpf)) {
                return f;
            }
        }
        throw new ValidacaoException("Funcionário não encontrado.");
    }

    //@ ensures \result != null;
    public /*@ pure @*/ Funcionario buscarFuncionarioPorMatricula(int matricula) throws ValidacaoException {
        for (Funcionario f : funcionarios) {
            if (f.getMatricula() == matricula) {
                return f;
            }
        }
        throw new ValidacaoException("Funcionário não encontrado.");
    }

    public void removerFuncionario(String cpf) throws ValidacaoException {
        Funcionario f = buscarFuncionarioPorCpf(cpf);
        funcionarios.remove(f);
    }

    public void atualizarDadosFuncionario(String cpf, String novoEndereco, String novoTelefone,
                                          String novoCargo, double novoSalario) throws ValidacaoException {

        Funcionario funcionario = buscarFuncionarioPorCpf(cpf);

        if (novoEndereco != null && !novoEndereco.isEmpty())
            funcionario.setEndereco(novoEndereco);

        if (novoTelefone != null && !novoTelefone.isEmpty())
            funcionario.setTelefone(novoTelefone);

        if (novoCargo != null && !novoCargo.isEmpty())
            funcionario.setCargo(novoCargo);

        if (novoSalario >= 0)
            funcionario.setSalario(novoSalario);
    }

    public List<Funcionario> listarFuncionarios() {
        return funcionarios;
    }

    // ========================= CONTAS =========================

    //@ public normal_behavior
    //@   requires cpfCliente != null;
    //@   requires existeCliente(cpfCliente);
    //@   requires !jaTemContaCorrente(cpfCliente);
    //@   requires limiteInicial >= 0;
    //@   assignable contas, numerosUsados;
    //@   ensures contas.size() == \old(contas.size()) + 1;
    //@   ensures \result != null;
    //@   ensures \result instanceof ContaCorrente;
    //@ also
    //@ public exceptional_behavior
    //@   requires !existeCliente(cpfCliente) || jaTemContaCorrente(cpfCliente);
    //@   signals_only ValidacaoException;
    public Conta criarContaCorrente(String cpfCliente, double limiteInicial) throws ValidacaoException {
        Cliente cliente = buscarClientePorCpf(cpfCliente);

        if (jaTemContaCorrente(cpfCliente)) {
            throw new ValidacaoException("Cliente já possui uma conta corrente.");
        }

        int numero = gerarNumeroContaUnico();
        Conta conta = new ContaCorrente(numero, 0.0, cliente, limiteInicial);
        contas.add(conta);
        cliente.adicionarConta(conta);
        return conta;
    }

    //@ public normal_behavior
    //@   requires cpfCliente != null;
    //@   requires existeCliente(cpfCliente);
    //@   requires !jaTemContaPoupanca(cpfCliente);
    //@   assignable contas, numerosUsados;
    //@   ensures contas.size() == \old(contas.size()) + 1;
    //@   ensures \result != null;
    //@   ensures \result instanceof ContaPoupanca;
    //@ also
    //@ public exceptional_behavior
    //@   requires !existeCliente(cpfCliente) || jaTemContaPoupanca(cpfCliente);
    //@   signals_only ValidacaoException;
    public Conta criarContaPoupanca(String cpfCliente) throws ValidacaoException {
        Cliente cliente = buscarClientePorCpf(cpfCliente);

        if (jaTemContaPoupanca(cpfCliente)) {
            throw new ValidacaoException("Cliente já possui uma conta poupança.");
        }

        int numero = gerarNumeroContaUnico();
        double taxaRendimentoPadrao = 0.5;
        Conta conta = new ContaPoupanca(numero, 0.0, cliente, taxaRendimentoPadrao);
        contas.add(conta);
        cliente.adicionarConta(conta);
        return conta;
    }

    //@ public normal_behavior
    //@   requires cpfCliente != null;
    //@   requires existeCliente(cpfCliente);
    //@   assignable contas, numerosUsados;
    //@   ensures contas.size() == \old(contas.size()) + 1;
    //@   ensures \result != null;
    //@   ensures \result instanceof ContaInvestimento;
    public Conta criarContaInvestimento(String cpfCliente) throws ValidacaoException {
        Cliente cliente = buscarClientePorCpf(cpfCliente);

        int numero = gerarNumeroContaUnico();
        Conta conta = new ContaInvestimento(numero, 0.0, cliente);
        contas.add(conta);
        cliente.adicionarConta(conta);
        return conta;
    }

    //@ public normal_behavior
    //@   requires contaExiste(numero);
    //@   ensures \result != null;
    //@   ensures \result.getNumero() == numero;
    //@ also
    //@ public exceptional_behavior
    //@   requires !contaExiste(numero);
    //@   signals_only ValidacaoException;
    public /*@ pure @*/ Conta buscarContaPorNumero(int numero) throws ValidacaoException {
        for (Conta c : contas) {
            if (c.getNumero() == numero) {
                return c;
            }
        }
        throw new ValidacaoException("Conta não encontrada.");
    }

    public void atualizarLimiteContaCorrente(int numeroConta, double novoLimite) throws ValidacaoException {
        if (novoLimite < 0) {
            throw new ValidacaoException("O limite não pode ser negativo.");
        }

        Conta conta = buscarContaPorNumero(numeroConta);

        if (conta instanceof ContaCorrente) {
            ((ContaCorrente) conta).setLimiteChequeEspecial(novoLimite);
        } else {
            throw new ValidacaoException("Esta conta não é uma Conta Corrente.");
        }
    }

    public void atualizarTaxaPoupanca(int numeroConta, double novaTaxa) throws ValidacaoException {
        if (novaTaxa <= 0) {
            throw new ValidacaoException("A taxa de rendimento deve ser positiva.");
        }

        Conta conta = buscarContaPorNumero(numeroConta);

        if (conta instanceof ContaPoupanca) {
            ((ContaPoupanca) conta).setTaxaRendimento(novaTaxa);
        } else {
            throw new ValidacaoException("Esta conta não é uma Conta Poupança.");
        }
    }

    //@ public normal_behavior
    //@   requires contaExiste(numeroConta);
    //@   // Requer que a conta tenha saldo zero para ser fechada
    //@   requires buscarContaPorNumero(numeroConta).getSaldo() == 0;
    //@   assignable contas, numerosUsados;
    //@   ensures !contaExiste(numeroConta);
    //@   ensures contas.size() == \old(contas.size()) - 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires !contaExiste(numeroConta) || buscarContaPorNumero(numeroConta).getSaldo() != 0;
    //@   signals_only ValidacaoException;
    public void removerConta(int numeroConta) throws ValidacaoException {
        Conta conta = buscarContaPorNumero(numeroConta);

        if (conta.getSaldo() > 0) {
            throw new ValidacaoException("Não é possível remover a conta. Saldo precisa ser 0.");
        }

        Cliente titular = conta.getTitular();

        if (titular != null && titular.getContas() != null) {
            titular.getContas().remove(conta);
        }

        contas.remove(conta);
        numerosUsados.remove(conta.getNumero());
    }

    //@ ensures \result == (\exists int i; 0 <= i && i < contas.size(); contas.get(i).getNumero() == numero);
    private /*@ spec_public pure helper @*/ boolean contaExiste(int numero) {
        for (Conta c : contas) {
            if (c.getNumero() == numero) {
                return true;
            }
        }
        return false;
    }

    //@ requires cpf != null;
    private /*@ spec_public pure helper @*/ boolean jaTemContaCorrente(String cpf) {
        for (Conta c : contas) {
            if (c instanceof ContaCorrente && c.getTitular().getCpf().equals(cpf)) {
                return true;
            }
        }
        return false;
    }

    //@ requires cpf != null;
    private /*@ spec_public pure helper @*/ boolean jaTemContaPoupanca(String cpf) {
        for (Conta c : contas) {
            if (c instanceof ContaPoupanca && c.getTitular().getCpf().equals(cpf)) {
                return true;
            }
        }
        return false;
    }

    // ========================= EMPRÉSTIMOS =========================

    //@ public normal_behavior
    //@   requires cliente != null;
    //@   requires valor > 0 && numParcelas > 0 && taxa >= 0;
    //@   requires valor <= cliente.getLimiteCredito();
    //@   assignable emprestimos;
    //@   ensures emprestimos.size() == \old(emprestimos.size()) + 1;
    //@   ensures \result != null;
    //@ also
    //@ public exceptional_behavior
    //@   requires valor > cliente.getLimiteCredito();
    //@   signals_only ValidacaoException;
    public Emprestimo criarEmprestimo(Cliente cliente, double valor,
                                      int numParcelas, double taxa)
            throws ValidacaoException {

        if (valor > cliente.getLimiteCredito()) {
            throw new ValidacaoException(
                    "Valor excede limite de crédito. Disponível: R$ " + cliente.getLimiteCredito()
            );
        }

        Emprestimo emp = new Emprestimo(valor, numParcelas, taxa, cliente);
        emprestimos.add(emp);
        cliente.adicionarEmprestimo(emp);

        return emp;
    }

    //@ requires emprestimo != null && conta != null;
    public void pagarParcelaEmprestimo(Emprestimo emprestimo, int numeroParcela,
                                       Conta conta)
            throws SaldoInsuficienteException, ValidacaoException {

        emprestimo.pagarParcela(numeroParcela, conta);

        Transacao t = new Transacao(
                TipoTransacao.PAGAMENTO_EMPRESTIMO,
                emprestimo.getValorParcela(numeroParcela),
                "Pagamento parcela " + numeroParcela + " de empréstimo",
                conta, null
        );

        auditoria.auditarTransacao(t);
    }

    // ========================= OPERAÇÕES =========================

    //@ requires contaExiste(numeroConta);
    //@ requires valor > 0;
    //@ assignable auditoria.transacoesAuditadas;
    public void realizarDeposito(int numeroConta, double valor)
            throws ValidacaoException {

        Conta conta = buscarContaPorNumero(numeroConta);
        conta.depositar(valor);

        Transacao t = new Transacao(
                TipoTransacao.DEPOSITO, valor,
                "Depósito em conta " + numeroConta,
                null, conta
        );

        auditoria.auditarTransacao(t);
    }

    //@ requires contaExiste(numeroConta);
    //@ requires valor > 0;
    //@ assignable auditoria.transacoesAuditadas;
    public void realizarSaque(int numeroConta, double valor)
            throws SaldoInsuficienteException, ValidacaoException {

        Conta conta = buscarContaPorNumero(numeroConta);
        conta.sacar(valor);

        Transacao t = new Transacao(
                TipoTransacao.SAQUE, valor,
                "Saque da conta " + numeroConta,
                conta, null
        );

        auditoria.auditarTransacao(t);
    }

    //@ public normal_behavior
    //@   requires contaExiste(numeroContaOrigem) && contaExiste(numeroContaDestino);
    //@   requires numeroContaOrigem != numeroContaDestino;
    //@   requires valor > 0;
    //@   requires buscarContaPorNumero(numeroContaOrigem).getSaldo() >= valor; // Simplificação para Conta Comum
    //@   assignable auditoria.transacoesAuditadas;
    //@   // Garante a consistência do saldo total do sistema (dinheiro sai de um e entra no outro)
    //@   ensures buscarContaPorNumero(numeroContaOrigem).getSaldo() == \old(buscarContaPorNumero(numeroContaOrigem).getSaldo()) - valor;
    //@   ensures buscarContaPorNumero(numeroContaDestino).getSaldo() == \old(buscarContaPorNumero(numeroContaDestino).getSaldo()) + valor;
    //@ also
    //@ public exceptional_behavior
    //@   requires numeroContaOrigem == numeroContaDestino || valor <= 0;
    //@   signals_only ValidacaoException, SaldoInsuficienteException;
    public void realizarTransferencia(int numeroContaOrigem,
                                      int numeroContaDestino,
                                      double valor)
            throws SaldoInsuficienteException, ValidacaoException {

        if (numeroContaOrigem == numeroContaDestino) {
            throw new ValidacaoException("Conta de origem e destino não podem ser iguais.");
        }

        if (valor <= 0) {
            throw new ValidacaoException("Valor da transferência deve ser positivo.");
        }

        Conta contaOrigem = buscarContaPorNumero(numeroContaOrigem);
        Conta contaDestino = buscarContaPorNumero(numeroContaDestino);

        contaOrigem.sacar(valor);

        try {
            contaDestino.depositar(valor);
        } catch (ValidacaoException e) {
            contaOrigem.depositar(valor);
            throw new ValidacaoException("Erro no depósito de destino. Transferência cancelada.");
        }

        Transacao t = new Transacao(
                TipoTransacao.TRANSFERENCIA_ENVIADA,
                valor,
                String.format("Transferência de %d para %d", numeroContaOrigem, numeroContaDestino),
                contaOrigem, contaDestino
        );

        auditoria.auditarTransacao(t);
    }

    // ========================= RELATÓRIOS =========================

    //@ ensures \result >= 0;
    //@ pure
    public double calcularSaldoTotalBanco() {
        double total = 0;
        //@ maintaining 0 <= i && i <= contas.size();
        //@ loop_writes i, total;
        //@ decreases contas.size() - i;
        for (int i = 0; i < contas.size(); i++) {
            total += contas.get(i).getSaldo();
        }
        return total;
    }

    //@ ensures \result != null;
    //@ pure
    public SistemaAuditoria getAuditoria() {
        return auditoria;
    }

    //@ ensures \result != null;
    //@ pure
    public List<Emprestimo> listarEmprestimos() {
        return new ArrayList<>(emprestimos);
    }

    //@ ensures \result != null;
    //@ pure
    public List<Conta> listarContas() {
        return new ArrayList<>(contas);
    }
}