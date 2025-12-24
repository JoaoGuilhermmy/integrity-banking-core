import java.util.InputMismatchException;
import java.util.List;
import java.util.Locale;
import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        Locale.setDefault(Locale.US);
        BancoService banco = new BancoService();
        Scanner scanner = new Scanner(System.in);

        while (true) {
            System.out.println("\n=== PAINEL DE CONTROLE DO BANCO (VERSÃO COMPLETA) ===");
            System.out.println("--- Clientes ---");
            System.out.println("1. Cadastrar Cliente");
            System.out.println("2. Listar Clientes");
            System.out.println("3. Atualizar Cliente");
            System.out.println("4. Remover Cliente");

            System.out.println("--- Contas ---");
            System.out.println("5. Criar Conta Corrente");
            System.out.println("6. Criar Conta Poupança");
            System.out.println("7. Criar Conta Investimento");
            System.out.println("8. Consultar Saldo e Detalhes");
            System.out.println("9. Remover Conta");

            System.out.println("--- Operações Básicas ---");
            System.out.println("10. Realizar Depósito");
            System.out.println("11. Realizar Saque");
            System.out.println("12. Realizar Transferência");

            System.out.println("--- Investimentos & Poupança ---");
            System.out.println("13. Aplicar Rendimento (Poupança)");
            System.out.println("14. Realizar Investimento (CDB, LCI, etc)");
            System.out.println("15. Resgatar Investimento");

            System.out.println("--- Empréstimos ---");
            System.out.println("16. Contratar Empréstimo");
            System.out.println("17. Pagar Parcela de Empréstimo");
            System.out.println("18. Listar Empréstimos");

            System.out.println("--- Administrativo & Auditoria ---");
            System.out.println("19. Cadastrar Funcionário");
            System.out.println("20. Listar Funcionários");
            System.out.println("21. Atualizar Limites/Taxas");
            System.out.println("22. [AUDITORIA] Ver Transações Auditadas");
            System.out.println("23. [AUDITORIA] Ver Alertas de Fraude");
            System.out.println("24. [RELATÓRIO] Saldo Total do Banco");

            System.out.println("-------------------------------------");
            System.out.println("0. Sair");
            System.out.print("Escolha uma opção: ");

            int opcao;
            try {
                opcao = scanner.nextInt();
                scanner.nextLine();
            } catch (InputMismatchException e) {
                System.err.println("Erro: digite apenas números inteiros.");
                scanner.nextLine();
                continue;
            }

            try {
                switch (opcao) {
                    case 1: {
                        System.out.print("Nome: ");
                        String nome = scanner.nextLine().trim();
                        System.out.print("CPF: ");
                        String cpf = scanner.nextLine().trim();
                        System.out.print("Endereço: ");
                        String end = scanner.nextLine().trim();
                        System.out.print("Telefone: ");
                        String tel = scanner.nextLine().trim();
                        System.out.print("Tipo (comum/premium): ");
                        String tipo = scanner.nextLine().trim();
                        System.out.print("Renda: ");
                        double renda = scanner.nextDouble();
                        banco.cadastrarCliente(nome, cpf, end, tel, tipo, renda);
                        System.out.println("Cliente cadastrado!");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 2: {
                        List<Cliente> lista = banco.listarClientes();
                        if (lista.isEmpty())
                            System.out.println("Nenhum cliente.");
                        for (Cliente c : lista) {
                            System.out.println(c.getDescricao() + " | Renda: " + c.getRenda() + " | Limite Crédito: "
                                    + c.getLimiteCredito());
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();

                        break;
                    }
                    case 3: {
                        System.out.print("CPF: ");
                        String cpf = scanner.nextLine();
                        System.out.print("Novo Endereço: ");
                        String end = scanner.nextLine();
                        System.out.print("Novo Telefone: ");
                        String tel = scanner.nextLine();
                        System.out.print("Nova Renda (-1 para manter): ");
                        double renda = scanner.nextDouble();
                        banco.atualizarDadosCliente(cpf, end, tel, null, renda);
                        System.out.println("Dados atualizados.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 4: {
                        System.out.print("CPF: ");
                        String cpf = scanner.nextLine();
                        banco.removerCliente(cpf);
                        System.out.println("Cliente removido.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 5: {
                        System.out.print("CPF do Titular: ");
                        String cpf = scanner.nextLine();
                        System.out.print("Limite Cheque Especial: ");
                        double lim = scanner.nextDouble();
                        Conta c = banco.criarContaCorrente(cpf, lim);
                        System.out.println("Conta Corrente criada: " + c.getNumero());
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 6: {
                        System.out.print("CPF do Titular: ");
                        String cpf = scanner.nextLine();
                        Conta c = banco.criarContaPoupanca(cpf);
                        System.out.println("Conta Poupança criada: " + c.getNumero());
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 7: {
                        System.out.print("CPF do Titular: ");
                        String cpf = scanner.nextLine();
                        Conta c = banco.criarContaInvestimento(cpf);
                        System.out.println("Conta Investimento criada: " + c.getNumero());
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 8: {
                        System.out.print("Número da Conta: ");
                        int num = scanner.nextInt();
                        Conta c = banco.buscarContaPorNumero(num);
                        System.out.printf("Conta %d | Saldo: R$ %.2f | Titular: %s%n",
                                c.getNumero(), c.getSaldo(), c.getTitular().getNome());
                        if (c instanceof ContaInvestimento) {
                            System.out.println(" (Conta de Investimento)");
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 9: {
                        System.out.print("Número da Conta: ");
                        int num = scanner.nextInt();
                        banco.removerConta(num);
                        System.out.println("Conta removida.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 10: {
                        System.out.print("Conta Destino: ");
                        int num = scanner.nextInt();
                        System.out.print("Valor: ");
                        double val = scanner.nextDouble();
                        banco.realizarDeposito(num, val);
                        System.out.println("Depósito realizado.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 11: {
                        System.out.print("Conta Origem: ");
                        int num = scanner.nextInt();
                        System.out.print("Valor: ");
                        double val = scanner.nextDouble();
                        banco.realizarSaque(num, val);
                        System.out.println("Saque realizado.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 12: {
                        System.out.print("Conta Origem: ");
                        int orig = scanner.nextInt();
                        System.out.print("Conta Destino: ");
                        int dest = scanner.nextInt();
                        System.out.print("Valor: ");
                        double val = scanner.nextDouble();
                        banco.realizarTransferencia(orig, dest, val);
                        System.out.println("Transferência realizada.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 13: {
                        System.out.print("Conta Poupança: ");
                        int num = scanner.nextInt();
                        Conta c = banco.buscarContaPorNumero(num);
                        if (c instanceof ContaPoupanca cp) {
                            cp.renderJuros();
                            System.out.println("Juros aplicados. Novo saldo: " + cp.getSaldo());
                        } else {
                            System.out.println("Essa conta não é poupança.");
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 14: {
                        System.out.print("Conta Investimento: ");
                        int num = scanner.nextInt();
                        Conta c = banco.buscarContaPorNumero(num);
                        if (c instanceof ContaInvestimento ci) {
                            System.out.println("Tipos: 1-CDB, 2-TESOURO, 3-LCI, 4-LCA, 5-FUNDO");
                            System.out.print("Escolha: ");
                            int t = scanner.nextInt();
                            System.out.print("Valor: ");
                            double val = scanner.nextDouble();

                            TipoInvestimento tipo = TipoInvestimento.values()[t - 1];
                            ci.investir(tipo, val);
                            System.out.println("Investimento realizado em " + tipo);
                        } else {
                            System.out.println("Conta inválida para investimento.");
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 15: {
                        System.out.print("Conta Investimento: ");
                        int num = scanner.nextInt();
                        Conta c = banco.buscarContaPorNumero(num);
                        if (c instanceof ContaInvestimento ci) {
                            List<Investimento> carteira = ci.getCarteira();
                            for (int i = 0; i < carteira.size(); i++) {
                                System.out.println(i + ": " + carteira.get(i).getResumo());
                            }
                            System.out.print("Índice para resgate: ");
                            int idx = scanner.nextInt();
                            ci.resgatar(idx);
                            System.out.println("Resgate realizado.");
                        } else {
                            System.out.println("Conta inválida.");
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 16: {
                        System.out.print("CPF do Cliente: ");
                        Scanner sc2 = new Scanner(System.in);
                        String cpf = sc2.nextLine();
                        Cliente cli = banco.buscarClientePorCpf(cpf);
                        System.out.print("Valor: ");
                        double val = scanner.nextDouble();
                        System.out.print("Parcelas: ");
                        int parc = scanner.nextInt();
                        System.out.print("Taxa Juros Mensal: ");
                        double taxa = scanner.nextDouble();
                        banco.criarEmprestimo(cli, val, parc, taxa);
                        System.out.println("Empréstimo contratado!");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 17: {
                        System.out.print("CPF do Cliente: ");
                        Scanner sc2 = new Scanner(System.in);
                        String cpf = sc2.nextLine();
                        Cliente cli = banco.buscarClientePorCpf(cpf);
                        List<Emprestimo> emps = cli.getEmprestimos();
                        if (emps.isEmpty()) {
                            System.out.println("Cliente não tem empréstimos.");
                            break;
                        }
                        for (int i = 0; i < emps.size(); i++) {
                            System.out.printf("Empréstimo %d: Valor Total %.2f - Saldo Devedor %.2f%n",
                                    i, emps.get(i).getValorTotal(), emps.get(i).getSaldoDevedor());
                        }
                        System.out.print("Escolha o empréstimo (índice): ");
                        int idx = scanner.nextInt();
                        System.out.print("Número da Parcela a pagar: ");
                        int numParc = scanner.nextInt();
                        System.out.print("Conta para débito (número): ");
                        int numConta = scanner.nextInt();
                        Conta contaPagamento = banco.buscarContaPorNumero(numConta);
                        banco.pagarParcelaEmprestimo(emps.get(idx), numParc, contaPagamento);
                        System.out.println("Parcela paga com sucesso.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 18: {
                        List<Emprestimo> lista = banco.listarEmprestimos();
                        for (Emprestimo e : lista) {
                            System.out.printf("Cliente: %s | Valor: %.2f | Restante: %.2f%n",
                                    e.getCliente().getNome(), e.getValorTotal(), e.getSaldoDevedor());
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 19: {
                        System.out.print("Nome: ");
                        Scanner sc2 = new Scanner(System.in);
                        String nome = sc2.nextLine();
                        System.out.print("CPF: ");
                        String cpf = sc2.nextLine();
                        System.out.print("Endereço: ");
                        String end = sc2.nextLine();
                        System.out.print("Telefone: ");
                        String tel = sc2.nextLine();
                        System.out.print("Matrícula: ");
                        int mat = scanner.nextInt();
                        System.out.print("Cargo: ");
                        Scanner sc3 = new Scanner(System.in);
                        String cargo = sc3.nextLine();
                        System.out.print("Salário: ");
                        double sal = scanner.nextDouble();
                        banco.cadastrarFuncionario(nome, cpf, end, tel, mat, cargo, sal);
                        System.out.println("Funcionário cadastrado.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 20: {
                        for (Funcionario f : banco.listarFuncionarios()) {
                            System.out.println(f.getDescricao());
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 21: {
                        System.out.print("Número da Conta: ");
                        int num = scanner.nextInt();
                        Conta c = banco.buscarContaPorNumero(num);
                        if (c instanceof ContaCorrente cc) {
                            System.out.print("Novo Limite: ");
                            double lim = scanner.nextDouble();
                            banco.atualizarLimiteContaCorrente(num, lim);
                        } else if (c instanceof ContaPoupanca cp) {
                            System.out.print("Nova Taxa: ");
                            double taxa = scanner.nextDouble();
                            banco.atualizarTaxaPoupanca(num, taxa);
                        } else {
                            System.out.println("Conta não permite alteração de taxas/limites.");
                        }
                        System.out.println("Atualizado.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 22: {
                        System.out.println("--- LOG DE AUDITORIA ---");
                        List<Transacao> logs = banco.getAuditoria().getTransacoesAuditadas();
                        for (Transacao t : logs) {
                            System.out.println(t);
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 23: {
                        System.out.println("--- ALERTAS DE SEGURANÇA ---");
                        List<String> alertas = banco.getAuditoria().getAlertas();
                        if (alertas.isEmpty())
                            System.out.println("Sistema seguro. Nenhum alerta.");
                        for (String s : alertas) {
                            System.err.println(s);
                        }
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 24: {
                        System.out.printf("Saldo Total do Banco: R$ %.2f%n",
                                banco.calcularSaldoTotalBanco());
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        break;
                    }
                    case 0:
                        System.out.println("Saindo...");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                        return;
                    default:
                        System.out.println("Opção inválida.");
                        Thread.sleep(3000);
                        System.out.print("\033[H\033[2J");
                        System.out.flush();
                }

            } catch (ValidacaoException | SaldoInsuficienteException e) {
                System.err.println("ERRO DE NEGÓCIO: " + e.getMessage());
            } catch (Exception e) {
                System.err.println("ERRO DE SISTEMA: " + e.getMessage());
                e.printStackTrace();
                scanner.nextLine();
            }
        }
    }
}
