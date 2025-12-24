# 🏦 Sistema Bancário Java com JML Annotations

<div align="center">

![Java](https://img.shields.io/badge/Java-11+-orange?style=for-the-badge&logo=java)
![JML](https://img.shields.io/badge/JML-Annotations-blue?style=for-the-badge)
![Status](https://img.shields.io/badge/Status-Em%20Desenvolvimento-yellow?style=for-the-badge)
![License](https://img.shields.io/badge/License-MIT-green?style=for-the-badge)

**Sistema bancário completo desenvolvido em Java com anotações JML para verificação formal de software**

[📖 Documentação](#documentação) • [🚀 Instalação](#instalação) • [💡 Funcionalidades](#funcionalidades) • [🏗️ Arquitetura](#arquitetura)

</div>

---

## 📋 Sobre o Projeto

Este projeto é um **sistema bancário robusto** desenvolvido em Java que implementa funcionalidades completas de gestão bancária. O diferencial está na utilização de **anotações JML (Java Modeling Language)** para especificações formais de comportamento, demonstrando boas práticas de engenharia de software e preocupação com qualidade de código.

### 🎯 Objetivos

- Demonstrar domínio de **Programação Orientada a Objetos** avançada
- Implementar **Design Patterns** e princípios SOLID
- Utilizar **JML** para contratos formais e verificação de software
- Criar um sistema com **mínimo de erros possíveis** através de especificações formais
- Aplicar tratamento robusto de exceções e validações

### ⚠️ Nota sobre JML

> **Importante:** As anotações JML estão em fase de desenvolvimento e refinamento. Algumas especificações podem apresentar inconsistências. O foco principal é demonstrar conhecimento em técnicas avançadas de verificação formal de software e intenção de criar código confiável através de contratos bem definidos.

---

## ✨ Funcionalidades

### 👥 Gestão de Clientes
- ✅ Cadastro completo com validação de CPF
- ✅ Categorias: **Comum** e **Premium**
- ✅ Cálculo automático de limite de crédito baseado na renda
- ✅ Histórico completo de transações por cliente
- ✅ Atualização de dados cadastrais
- ✅ Remoção com verificação de contas ativas

### 💳 Contas Bancárias

#### Conta Corrente
- Cheque especial configurável
- Controle de dias em débito
- Cálculo de juros sobre saldo negativo
- Tarifa diferenciada por tipo de cliente

#### Conta Poupança
- Rendimento percentual automático
- Taxa de rendimento configurável
- Sem tarifa de manutenção
- Aplicação de juros mensais

#### Conta Investimento
- Suporte a múltiplos tipos de investimento
- Carteira de investimentos completa
- Cálculo automático de rentabilidade
- Controle de período de carência

### 💰 Operações Financeiras
- 🔄 **Depósitos** com validação de valores
- 💵 **Saques** com verificação de saldo e limites
- 🔀 **Transferências** entre contas com rollback automático
- 📊 **Extrato** completo de movimentações
- 💳 **Tarifas** diferenciadas por tipo de conta e cliente

### 📈 Sistema de Investimentos

Tipos disponíveis:
- **CDB** - 0.8% a.m., carência de 90 dias
- **Tesouro Direto** - 0.6% a.m., carência de 180 dias
- **LCI** - 0.7% a.m., carência de 90 dias
- **LCA** - 0.7% a.m., carência de 90 dias
- **Fundo Renda Fixa** - 0.5% a.m., carência de 30 dias

Funcionalidades:
- Aplicação direta da conta investimento
- Cálculo de rendimento com juros compostos
- Resgate com verificação de carência
- Histórico de investimentos ativos e resgatados

### 🏦 Empréstimos
- 📝 Contratação com análise de limite de crédito
- 💵 Sistema de parcelas com juros compostos
- 📅 Controle de vencimento e pagamentos
- ⚠️ Multa e juros por atraso automáticos
- 📊 Acompanhamento de saldo devedor

### 🔍 Auditoria & Compliance
- 📋 Log completo de todas as transações
- 🚨 Detecção automática de operações suspeitas
- ⚡ Alertas para transações de alto valor (≥ R$ 50.000)
- 📄 Marcação de operações que requerem documentação (> R$ 10.000)
- ✅ Verificação de conformidade por cliente

### 👔 Gestão de Funcionários
- Cadastro com matrícula única
- Controle de cargo e salário
- Cálculo de bonificações (10% do salário)
- Dados completos de contato

---

## 🏗️ Arquitetura

### Estrutura de Classes

```
┌─────────────────────────────────────────────────────────────┐
│                         Pessoa (Abstract)                    │
│  - nome, cpf, endereco, telefone                            │
└────────────────────────┬────────────────────────────────────┘
                         │
            ┌────────────┴────────────┐
            │                         │
   ┌────────▼────────┐       ┌───────▼──────────┐
   │    Cliente      │       │   Funcionario    │
   ├─────────────────┤       ├──────────────────┤
   │ - id            │       │ - matricula      │
   │ - tipoCliente   │       │ - cargo          │
   │ - renda         │       │ - salario        │
   │ - contas        │       └──────────────────┘
   │ - emprestimos   │
   └────────┬────────┘
            │
            │ 1..*
            │
   ┌────────▼──────────────────────┐
   │      Conta (Abstract)         │
   ├───────────────────────────────┤
   │ - numero                      │
   │ - saldo                       │
   │ - titular: Cliente            │
   │ - historicoTransacoes         │
   ├───────────────────────────────┤
   │ + depositar()                 │
   │ + sacar() (abstract)          │
   │ + calcularTarifa() (abstract) │
   └───────────┬───────────────────┘
               │
    ┌──────────┼──────────────┐
    │          │              │
┌───▼────┐ ┌──▼────┐ ┌───────▼────────┐
│Corrente│ │Poupança│ │ Investimento   │
├────────┤ ├────────┤ ├────────────────┤
│-limite │ │-taxa   │ │-carteira       │
│Cheque  │ │Rendi-  │ │:List<Investi-  │
│Especial│ │mento   │ │mento>          │
└────────┘ └────────┘ └────────────────┘
```

### Design Patterns Implementados

| Pattern | Aplicação | Benefício |
|---------|-----------|-----------|
| **Service Layer** | `BancoService` centraliza lógica de negócio | Separação de responsabilidades |
| **Factory Method** | Criação de diferentes tipos de conta | Extensibilidade |
| **Strategy** | Cálculo de tarifas por tipo de conta | Flexibilidade de cálculo |
| **Template Method** | Classe abstrata `Conta` | Reutilização de código |

### Principais Classes

#### 🎯 BancoService
**Responsabilidade:** Orquestrar todas as operações do sistema

```java
public class BancoService {
    // Gerencia coleções de entidades
    private List<Cliente> clientes;
    private List<Conta> contas;
    private List<Funcionario> funcionarios;
    private List<Emprestimo> emprestimos;
    private SistemaAuditoria auditoria;
    
    // Operações principais
    public Cliente cadastrarCliente(...)
    public Conta criarContaCorrente(...)
    public void realizarTransferencia(...)
    public Emprestimo criarEmprestimo(...)
}
```

#### 👤 Cliente & Funcionario
**Herdam de:** `Pessoa` (classe abstrata)

**Diferencial do Cliente:**
- Cálculo automático de limite de crédito
- Gestão de múltiplas contas
- Histórico de transações
- Controle de empréstimos ativos

#### 💳 Hierarquia de Contas
**Classe Base:** `Conta` (abstrata)

**Implementações:**
1. `ContaCorrente` - Com cheque especial
2. `ContaPoupanca` - Com rendimento
3. `ContaInvestimento` - Com carteira de investimentos

Cada tipo implementa:
- `sacar()` - Lógica específica de saque
- `calcularTarifa()` - Tarifa diferenciada

#### 📝 Transacao
**Características:**
- Imutável (dados não podem ser alterados)
- ID único sequencial
- Timestamp automático
- Referências para contas origem/destino
- Tipos definidos por enum `TipoTransacao`

#### 🔍 SistemaAuditoria
**Funcionalidades:**
- Registro de todas as transações
- Detecção de padrões suspeitos
- Geração de alertas
- Verificação de conformidade

---

## 🚀 Instalação

### Pré-requisitos

- ☕ **Java JDK 11** ou superior
- 🛠️ **IDE** (IntelliJ IDEA, Eclipse, VS Code com Extension Pack for Java)
- 📦 **Git** para clonar o repositório

### Passos de Instalação

#### 1️⃣ Clone o repositório

```bash
git clone https://github.com/seu-usuario/sistema-bancario-java.git
cd sistema-bancario-java
```

#### 2️⃣ Compilar via linha de comando

```bash
# Criar diretório de saída
mkdir -p bin

# Compilar todos os arquivos Java
javac -d bin src/*.java
```

#### 3️⃣ Executar a aplicação

```bash
java -cp bin Main
```

### Usando uma IDE

#### IntelliJ IDEA
1. `File` → `Open` → Selecione a pasta do projeto
2. A IDE detectará automaticamente os arquivos Java
3. Localize `Main.java` no explorador de arquivos
4. Clique com botão direito → `Run 'Main.main()'`

#### Eclipse
1. `File` → `Import` → `Existing Projects into Workspace`
2. Selecione a pasta do projeto
3. Localize `Main.java` no Package Explorer
4. Clique com botão direito → `Run As` → `Java Application`

#### VS Code
1. Abra a pasta do projeto
2. Instale a extensão "Extension Pack for Java"
3. Abra `Main.java`
4. Clique em `Run` acima do método `main()`

---

## 💻 Como Usar

### Interface de Menu

O sistema apresenta um menu interativo completo no terminal:

```
=== PAINEL DE CONTROLE DO BANCO ===

--- Clientes ---
1. Cadastrar Cliente
2. Listar Clientes
3. Atualizar Cliente
4. Remover Cliente

--- Contas ---
5. Criar Conta Corrente
6. Criar Conta Poupança
7. Criar Conta Investimento
8. Consultar Saldo e Detalhes
9. Remover Conta

--- Operações Básicas ---
10. Realizar Depósito
11. Realizar Saque
12. Realizar Transferência

--- Investimentos & Poupança ---
13. Aplicar Rendimento (Poupança)
14. Realizar Investimento
15. Resgatar Investimento

--- Empréstimos ---
16. Contratar Empréstimo
17. Pagar Parcela de Empréstimo
18. Listar Empréstimos

--- Administrativo & Auditoria ---
19. Cadastrar Funcionário
20. Listar Funcionários
21. Atualizar Limites/Taxas
22. [AUDITORIA] Ver Transações Auditadas
23. [AUDITORIA] Ver Alertas de Fraude
24. [RELATÓRIO] Saldo Total do Banco

0. Sair
```

### Exemplos Práticos

#### 📝 Cadastrar um Cliente

```
1. Selecione opção: 1
2. Nome: João Silva
3. CPF: 123.456.789-00
4. Endereço: Rua A, 123
5. Telefone: 83999887766
6. Tipo: premium (ou comum)
7. Renda: 5000

✅ Cliente cadastrado com sucesso!
💰 Limite de crédito calculado: R$ 25.000,00 (renda × 5 para premium)
```

#### 🏦 Criar Conta e Realizar Operações

```bash
# Criar conta corrente
Opção: 5
CPF: 123.456.789-00
Limite Cheque Especial: 1000
✅ Conta criada: 1234

# Realizar depósito
Opção: 10
Conta: 1234
Valor: 500
✅ Depósito realizado

# Realizar saque
Opção: 11
Conta: 1234
Valor: 200
✅ Saque realizado
💵 Saldo atual: R$ 300,00
```

#### 📈 Fazer um Investimento

```bash
# Criar conta investimento
Opção: 7
CPF: 123.456.789-00
✅ Conta Investimento criada: 5678

# Depositar valor inicial
Opção: 10
Conta: 5678
Valor: 10000

# Realizar investimento
Opção: 14
Conta: 5678
Tipos: 1-CDB, 2-TESOURO, 3-LCI, 4-LCA, 5-FUNDO
Escolha: 1 (CDB)
Valor: 5000
✅ Investimento realizado em CDB
📊 Rentabilidade: 0.8% ao mês
⏳ Carência: 90 dias
```

#### 💰 Contratar Empréstimo

```bash
Opção: 16
CPF: 123.456.789-00
Valor: 10000
Parcelas: 12
Taxa Juros Mensal: 2.5
✅ Empréstimo contratado!
📋 Valor da parcela: R$ 941,67
💳 Primeiro vencimento: [data+30dias]
```

### Uso Programático

```java
// Inicializar o sistema
BancoService banco = new BancoService();

// Cadastrar cliente premium
Cliente cliente = banco.cadastrarCliente(
    "Maria Santos",
    "987.654.321-00",
    "Av. Principal, 456",
    "83988776655",
    "premium",
    8000.00
);

// Criar conta corrente com limite
Conta contaCorrente = banco.criarContaCorrente(
    "987.654.321-00",
    2000.00  // Limite cheque especial
);

// Realizar operações
banco.realizarDeposito(contaCorrente.getNumero(), 1000.00);
banco.realizarSaque(contaCorrente.getNumero(), 300.00);

// Criar conta poupança
Conta poupanca = banco.criarContaPoupanca("987.654.321-00");
banco.realizarDeposito(poupanca.getNumero(), 5000.00);

// Aplicar rendimento
if (poupanca instanceof ContaPoupanca) {
    ((ContaPoupanca) poupanca).renderJuros();
}

// Transferência entre contas
banco.realizarTransferencia(
    contaCorrente.getNumero(),
    poupanca.getNumero(),
    500.00
);

// Consultar auditoria
List<Transacao> transacoes = banco.getAuditoria()
    .getTransacoesAuditadas();
List<String> alertas = banco.getAuditoria()
    .getAlertas();
```

---

## 🔐 JML e Verificação Formal

### O que é JML?

**JML (Java Modeling Language)** é uma linguagem de especificação comportamental para Java que permite:
- ✅ Definir **pré-condições** (requisitos para executar um método)
- ✅ Definir **pós-condições** (garantias após execução)
- ✅ Especificar **invariantes** (propriedades que sempre devem ser verdadeiras)
- ✅ Documentar **contratos** formais entre métodos e chamadores

### Por que usar JML?

1. **Documentação Precisa** - Especificações formais são mais claras que comentários
2. **Detecção de Bugs** - Ferramentas podem verificar automaticamente o código
3. **Melhor Design** - Pensar em contratos melhora a arquitetura
4. **Confiabilidade** - Código com contratos formais tende a ter menos erros

### Exemplo de Especificação JML

```java
//@ requires valor > 0;
//@ requires valor <= getSaldo() + limiteChequeEspecial;
//@ ensures getSaldo() == \old(getSaldo()) - valor;
//@ signals (SaldoInsuficienteException e) valor > getSaldo() + limiteChequeEspecial;
public void sacar(double valor) throws SaldoInsuficienteException {
    if (valor <= 0) {
        throw new ValidacaoException("Valor deve ser positivo");
    }
    
    double saldoDisponivel = getSaldo() + limiteChequeEspecial;
    
    if (valor > saldoDisponivel) {
        throw new SaldoInsuficienteException(
            "Saldo insuficiente. Disponível: R$ " + saldoDisponivel
        );
    }
    
    setSaldo(getSaldo() - valor);
}
```

**Explicação:**
- `requires` - Pré-condições que devem ser verdadeiras antes da execução
- `ensures` - Pós-condições garantidas após execução bem-sucedida
- `signals` - Especifica quando exceções são lançadas
- `\old()` - Referencia o valor anterior de uma variável

### Ferramentas de Verificação

Para verificar as especificações JML, você pode usar:

- **OpenJML** - Verificador estático para JML
- **KeY** - Provador de teoremas para Java+JML
- **ESC/Java2** - Extended Static Checker

```bash
# Exemplo de verificação com OpenJML (quando configurado)
openjml -check src/Conta.java
```

### Status do JML neste Projeto

> ⚠️ **Em Desenvolvimento:** As especificações JML estão sendo refinadas e podem conter inconsistências. O objetivo é demonstrar conhecimento da técnica e intenção de criar software verificável formalmente.

**Próximos Passos:**
- [ ] Adicionar especificações JML completas em todas as classes
- [ ] Configurar OpenJML para verificação automática
- [ ] Corrigir inconsistências nas especificações existentes
- [ ] Adicionar invariantes de classe completos
- [ ] Documentar casos de teste baseados em contratos

---

## 🧪 Tratamento de Exceções

### Hierarquia de Exceções

```
Exception
   │
   ├─ ValidacaoException
   │  └─ Erros de validação de negócio
   │
   └─ SaldoInsuficienteException
      └─ Saldo insuficiente para operação
```

### Exemplos de Tratamento

```java
try {
    banco.realizarSaque(numeroConta, 1000.00);
} catch (SaldoInsuficienteException e) {
    System.err.println("❌ " + e.getMessage());
    // Saldo insuficiente. Disponível: R$ 500.00
} catch (ValidacaoException e) {
    System.err.println("⚠️ " + e.getMessage());
    // O valor do saque deve ser positivo
}
```

### Validações Implementadas

- ✅ CPF único no cadastro
- ✅ Valores positivos em operações
- ✅ Saldo suficiente para saques
- ✅ Contas existentes em transferências
- ✅ Limite de crédito em empréstimos
- ✅ Período de carência em investimentos
- ✅ Parcelas válidas em empréstimos
- ✅ Dados obrigatórios no cadastro

---

## 📊 Diagramas

### Fluxo de Transferência

```
┌─────────────┐
│   Cliente   │
│  solicita   │
│transferência│
└──────┬──────┘
       │
       ▼
┌─────────────────────────────────┐
│      BancoService               │
│  realizarTransferencia()        │
└──────┬──────────────────────────┘
       │
       ├─── 1. Validar contas
       │
       ├─── 2. Sacar da origem
       │         │
       │         ├─ Verificar saldo
       │         └─ Deduzir valor
       │
       ├─── 3. Depositar no destino
       │         │
       │         └─ Adicionar valor
       │
       ├─── 4. Registrar transação
       │         │
       │         └─ SistemaAuditoria
       │
       └─── 5. Se erro → Rollback
```

### Ciclo de Vida de um Investimento

```
┌──────────────┐
│  APLICAÇÃO   │  ← Cliente investe valor
└──────┬───────┘
       │
       ▼
┌──────────────┐
│    ATIVO     │  ← Rendimento calculado diariamente
│ (Carência)   │    Não pode resgatar
└──────┬───────┘
       │
       │ Após período de carência
       │
       ▼
┌──────────────┐
│    ATIVO     │  ← Pode resgatar a qualquer momento
│ (Disponível) │    Rendimento continua
└──────┬───────┘
       │
       │ Cliente solicita resgate
       │
       ▼
┌──────────────┐
│  RESGATADO   │  ← Valor + rendimento volta para conta
└──────────────┘
```

---

## 🔧 Tecnologias e Conceitos

### Tecnologias

- ☕ **Java 11+** - Linguagem principal
- 📝 **JML** - Especificações formais
- 🧪 **Exceptions** - Tratamento robusto de erros
- 📦 **Collections Framework** - Gerenciamento de dados

### Conceitos Aplicados

#### Programação Orientada a Objetos
- ✅ Encapsulamento
- ✅ Herança
- ✅ Polimorfismo
- ✅ Abstração
- ✅ Classes abstratas e interfaces

#### Princípios SOLID
- **S** - Single Responsibility: Cada classe tem uma responsabilidade clara
- **O** - Open/Closed: Extensível sem modificar código existente
- **L** - Liskov Substitution: Subtipos podem substituir tipos base
- **I** - Interface Segregation: Interfaces específicas e coesas
- **D** - Dependency Inversion: Depende de abstrações, não implementações

#### Boas Práticas
- 📋 Validação de entrada
- 🔒 Encapsulamento de dados
- 🎯 Métodos coesos e com propósito único
- 📝 Documentação via JML
- ⚠️ Tratamento apropriado de exceções
- 🔄 Imutabilidade onde apropriado

---

## 📈 Melhorias Futuras

### Curto Prazo
- [ ] Completar especificações JML em todas as classes
- [ ] Adicionar testes unitários com JUnit
- [ ] Implementar persistência de dados (banco de dados)
- [ ] Criar interface gráfica (JavaFX ou Swing)

### Médio Prazo
- [ ] API REST com Spring Boot
- [ ] Autenticação e autorização
- [ ] Relatórios em PDF
- [ ] Notificações por email/SMS
- [ ] Dashboard administrativo

### Longo Prazo
- [ ] Integração com APIs bancárias reais
- [ ] Sistema de pagamentos PIX
- [ ] App mobile (Android/iOS)
- [ ] Análise de crédito com Machine Learning
- [ ] Blockchain para auditoria

---

## 🤝 Contribuindo

Contribuições são bem-vindas! Se você quer melhorar este projeto:

1. Faça um Fork do projeto
2. Crie uma branch para sua feature (`git checkout -b feature/MinhaFeature`)
3. Commit suas mudanças (`git commit -m 'Adiciona nova feature'`)
4. Push para a branch (`git push origin feature/MinhaFeature`)
5. Abra um Pull Request

### Áreas que precisam de ajuda
- 📝 Completar especificações JML
- 🧪 Adicionar testes unitários
- 📚 Melhorar documentação
- 🐛 Reportar e corrigir bugs
- ✨ Sugerir novas funcionalidades

---

## 📄 Licença

Este projeto está sob a licença MIT. Veja o arquivo [LICENSE](LICENSE) para mais detalhes.

---

## 👨‍💻 Autor

**João Guilhermmy**

- GitHub: https://github.com/JoaoGuilhermmy
- LinkedIn: www.linkedin.com/in/joão-guilhermmy-93661b29b
- Email: joaoguilhermmy2@gmail.com

---

## 🙏 Agradecimentos

- Comunidade Java pela excelente documentação
- Projeto OpenJML pelos recursos de verificação formal
- Todos que contribuíram com ideias e sugestões

---

<div align="center">

### ⭐ Se este projeto foi útil, considere dar uma estrela!

**Desenvolvido com ❤️ e muito ☕**

</div>
