# 🏦 Java Banking System with JML Annotations

<div align="center">

![Java](https://img.shields.io/badge/Java-11+-orange?style=for-the-badge&logo=java)
![JML](https://img.shields.io/badge/JML-Annotations-blue?style=for-the-badge)
![Status](https://img.shields.io/badge/Status-In%20Development-yellow?style=for-the-badge)
![License](https://img.shields.io/badge/License-MIT-green?style=for-the-badge)

**Complete banking system developed in Java with JML annotations for formal software verification**

[📖 Documentation](#documentation) • [🚀 Installation](#installation) • [💡 Features](#features) • [🏗️ Architecture](#architecture)

---

**[🇧🇷 Versão em Português](README.pt-BR.md)**

</div>

---

## 📋 About the Project

This project is a **robust banking system** developed in Java that implements complete bank management functionalities. The key differentiator is the use of **JML (Java Modeling Language) annotations** for formal behavior specifications, demonstrating software engineering best practices and code quality concerns.

### 🎯 Objectives

- Demonstrate mastery of advanced **Object-Oriented Programming**
- Implement **Design Patterns** and SOLID principles
- Use **JML** for formal contracts and software verification
- Create a system with **minimum possible errors** through formal specifications
- Apply robust exception handling and validations

### ⚠️ Note about JML

> **Important:** JML annotations are in development and refinement phase. Some specifications may present inconsistencies. The main focus is to demonstrate knowledge in advanced formal software verification techniques and intention to create reliable code through well-defined contracts.

---

## ✨ Features

### 👥 Customer Management
- ✅ Complete registration with CPF validation (Brazilian tax ID)
- ✅ Categories: **Standard** and **Premium**
- ✅ Automatic credit limit calculation based on income
- ✅ Complete transaction history per customer
- ✅ Customer data updates
- ✅ Removal with active account verification

### 💳 Bank Accounts

#### Checking Account
- Configurable overdraft protection
- Overdraft days tracking
- Interest calculation on negative balance
- Differentiated fees by customer type

#### Savings Account
- Automatic percentage yield
- Configurable interest rate
- No maintenance fee
- Monthly interest application

#### Investment Account
- Support for multiple investment types
- Complete investment portfolio
- Automatic profitability calculation
- Waiting period control

### 💰 Financial Operations
- 🔄 **Deposits** with value validation
- 💵 **Withdrawals** with balance and limit verification
- 🔀 **Transfers** between accounts with automatic rollback
- 📊 Complete **statement** of transactions
- 💳 **Fees** differentiated by account and customer type

### 📈 Investment System

Available types:
- **CDB** - 0.8% per month, 90-day waiting period
- **Treasury Direct** - 0.6% per month, 180-day waiting period
- **LCI** (Real Estate Credit Letter) - 0.7% per month, 90-day waiting period
- **LCA** (Agribusiness Credit Letter) - 0.7% per month, 90-day waiting period
- **Fixed Income Fund** - 0.5% per month, 30-day waiting period

Features:
- Direct application from investment account
- Compound interest yield calculation
- Redemption with waiting period verification
- History of active and redeemed investments

### 🏦 Loans
- 📝 Contracting with credit limit analysis
- 💵 Installment system with compound interest
- 📅 Due date and payment control
- ⚠️ Automatic late payment fees and interest
- 📊 Outstanding balance tracking

### 🔍 Audit & Compliance
- 📋 Complete log of all transactions
- 🚨 Automatic detection of suspicious operations
- ⚡ Alerts for high-value transactions (≥ $50,000 BRL)
- 📄 Marking of operations requiring documentation (> $10,000 BRL)
- ✅ Compliance verification per customer

### 👔 Employee Management
- Registration with unique employee ID
- Position and salary control
- Bonus calculation (10% of salary)
- Complete contact information

---

## 🏗️ Architecture

### Class Structure

```
┌─────────────────────────────────────────────────────────────┐
│                         Person (Abstract)                    │
│  - name, cpf, address, phone                                │
└────────────────────────┬────────────────────────────────────┘
                         │
            ┌────────────┴────────────┐
            │                         │
   ┌────────▼────────┐       ┌───────▼──────────┐
   │    Customer     │       │    Employee      │
   ├─────────────────┤       ├──────────────────┤
   │ - id            │       │ - employeeId     │
   │ - customerType  │       │ - position       │
   │ - income        │       │ - salary         │
   │ - accounts      │       └──────────────────┘
   │ - loans         │
   └────────┬────────┘
            │
            │ 1..*
            │
   ┌────────▼──────────────────────┐
   │      Account (Abstract)       │
   ├───────────────────────────────┤
   │ - accountNumber               │
   │ - balance                     │
   │ - holder: Customer            │
   │ - transactionHistory          │
   ├───────────────────────────────┤
   │ + deposit()                   │
   │ + withdraw() (abstract)       │
   │ + calculateFee() (abstract)   │
   └───────────┬───────────────────┘
               │
    ┌──────────┼──────────────┐
    │          │              │
┌───▼────┐ ┌──▼────┐ ┌───────▼────────┐
│Checking│ │Savings│ │  Investment    │
├────────┤ ├────────┤ ├────────────────┤
│-over-  │ │-interest│ │-portfolio      │
│draft   │ │Rate    │ │:List<Invest-   │
│Limit   │ │        │ │ment>           │
└────────┘ └────────┘ └────────────────┘
```

### Implemented Design Patterns

| Pattern | Application | Benefit |
|---------|-------------|---------|
| **Service Layer** | `BankingService` centralizes business logic | Separation of concerns |
| **Factory Method** | Creation of different account types | Extensibility |
| **Strategy** | Fee calculation by account type | Calculation flexibility |
| **Template Method** | `Account` abstract class | Code reuse |

### Main Classes

#### 🎯 BankingService
**Responsibility:** Orchestrate all system operations

```java
public class BancoService {
    // Manages entity collections
    private List<Cliente> clientes;        // customers
    private List<Conta> contas;            // accounts
    private List<Funcionario> funcionarios; // employees
    private List<Emprestimo> emprestimos;  // loans
    private SistemaAuditoria auditoria;    // audit system
    
    // Main operations
    public Cliente cadastrarCliente(...)     // register customer
    public Conta criarContaCorrente(...)     // create checking account
    public void realizarTransferencia(...)   // perform transfer
    public Emprestimo criarEmprestimo(...)   // create loan
}
```

#### 👤 Customer & Employee
**Inherit from:** `Person` (abstract class)

**Customer Differentials:**
- Automatic credit limit calculation
- Multiple account management
- Transaction history
- Active loan control

#### 💳 Account Hierarchy
**Base Class:** `Account` (abstract)

**Implementations:**
1. `CheckingAccount` - With overdraft protection
2. `SavingsAccount` - With interest yield
3. `InvestmentAccount` - With investment portfolio

Each type implements:
- `withdraw()` - Specific withdrawal logic
- `calculateFee()` - Differentiated fee

#### 📝 Transaction
**Characteristics:**
- Immutable (data cannot be changed)
- Unique sequential ID
- Automatic timestamp
- References to source/destination accounts
- Types defined by `TransactionType` enum

#### 🔍 AuditSystem
**Features:**
- Recording of all transactions
- Suspicious pattern detection
- Alert generation
- Compliance verification

---

## 🚀 Installation

### Prerequisites

- ☕ **Java JDK 11** or higher
- 🛠️ **IDE** (IntelliJ IDEA, Eclipse, VS Code with Extension Pack for Java)
- 📦 **Git** to clone the repository

### Installation Steps

#### 1️⃣ Clone the repository

```bash
git clone https://github.com/your-username/java-banking-system.git
cd java-banking-system
```

#### 2️⃣ Compile via command line

```bash
# Create output directory
mkdir -p bin

# Compile all Java files
javac -d bin src/*.java
```

#### 3️⃣ Run the application

```bash
java -cp bin Main
```

### Using an IDE

#### IntelliJ IDEA
1. `File` → `Open` → Select the project folder
2. The IDE will automatically detect Java files
3. Locate `Main.java` in the file explorer
4. Right-click → `Run 'Main.main()'`

#### Eclipse
1. `File` → `Import` → `Existing Projects into Workspace`
2. Select the project folder
3. Locate `Main.java` in Package Explorer
4. Right-click → `Run As` → `Java Application`

#### VS Code
1. Open the project folder
2. Install the "Extension Pack for Java" extension
3. Open `Main.java`
4. Click `Run` above the `main()` method

---

## 💻 How to Use

### Menu Interface

The system presents a complete interactive menu in the terminal:

```
=== BANK CONTROL PANEL ===

--- Customers ---
1. Register Customer
2. List Customers
3. Update Customer
4. Remove Customer

--- Accounts ---
5. Create Checking Account
6. Create Savings Account
7. Create Investment Account
8. Check Balance and Details
9. Remove Account

--- Basic Operations ---
10. Make Deposit
11. Make Withdrawal
12. Make Transfer

--- Investments & Savings ---
13. Apply Interest (Savings)
14. Make Investment
15. Redeem Investment

--- Loans ---
16. Contract Loan
17. Pay Loan Installment
18. List Loans

--- Administrative & Audit ---
19. Register Employee
20. List Employees
21. Update Limits/Rates
22. [AUDIT] View Audited Transactions
23. [AUDIT] View Fraud Alerts
24. [REPORT] Bank Total Balance

0. Exit
```

### Practical Examples

#### 📝 Register a Customer

```
1. Select option: 1
2. Name: John Smith
3. CPF: 123.456.789-00
4. Address: Main St, 123
5. Phone: +5583999887766
6. Type: premium (or standard)
7. Income: 5000

✅ Customer registered successfully!
💰 Credit limit calculated: $25,000.00 (income × 5 for premium)
```

#### 🏦 Create Account and Perform Operations

```bash
# Create checking account
Option: 5
CPF: 123.456.789-00
Overdraft Limit: 1000
✅ Account created: 1234

# Make deposit
Option: 10
Account: 1234
Amount: 500
✅ Deposit completed

# Make withdrawal
Option: 11
Account: 1234
Amount: 200
✅ Withdrawal completed
💵 Current balance: $300.00
```

#### 📈 Make an Investment

```bash
# Create investment account
Option: 7
CPF: 123.456.789-00
✅ Investment Account created: 5678

# Deposit initial amount
Option: 10
Account: 5678
Amount: 10000

# Make investment
Option: 14
Account: 5678
Types: 1-CDB, 2-TREASURY, 3-LCI, 4-LCA, 5-FUND
Choose: 1 (CDB)
Amount: 5000
✅ Investment made in CDB
📊 Profitability: 0.8% per month
⏳ Waiting period: 90 days
```

#### 💰 Contract a Loan

```bash
Option: 16
CPF: 123.456.789-00
Amount: 10000
Installments: 12
Monthly Interest Rate: 2.5
✅ Loan contracted!
📋 Installment amount: $941.67
💳 First due date: [date+30days]
```

### Programmatic Usage

```java
// Initialize the system
BancoService banco = new BancoService();

// Register premium customer
Cliente cliente = banco.cadastrarCliente(
    "Maria Santos",
    "987.654.321-00",
    "Main Avenue, 456",
    "+5583988776655",
    "premium",
    8000.00
);

// Create checking account with limit
Conta contaCorrente = banco.criarContaCorrente(
    "987.654.321-00",
    2000.00  // Overdraft limit
);

// Perform operations
banco.realizarDeposito(contaCorrente.getNumero(), 1000.00);
banco.realizarSaque(contaCorrente.getNumero(), 300.00);

// Create savings account
Conta poupanca = banco.criarContaPoupanca("987.654.321-00");
banco.realizarDeposito(poupanca.getNumero(), 5000.00);

// Apply interest
if (poupanca instanceof ContaPoupanca) {
    ((ContaPoupanca) poupanca).renderJuros();
}

// Transfer between accounts
banco.realizarTransferencia(
    contaCorrente.getNumero(),
    poupanca.getNumero(),
    500.00
);

// Query audit
List<Transacao> transacoes = banco.getAuditoria()
    .getTransacoesAuditadas();
List<String> alertas = banco.getAuditoria()
    .getAlertas();
```

---

## 🔐 JML and Formal Verification

### What is JML?

**JML (Java Modeling Language)** is a behavioral specification language for Java that allows:
- ✅ Define **preconditions** (requirements to execute a method)
- ✅ Define **postconditions** (guarantees after execution)
- ✅ Specify **invariants** (properties that must always be true)
- ✅ Document **formal contracts** between methods and callers

### Why use JML?

1. **Precise Documentation** - Formal specifications are clearer than comments
2. **Bug Detection** - Tools can automatically verify code
3. **Better Design** - Thinking about contracts improves architecture
4. **Reliability** - Code with formal contracts tends to have fewer errors

### JML Specification Example

```java
//@ requires amount > 0;
//@ requires amount <= getBalance() + overdraftLimit;
//@ ensures getBalance() == \old(getBalance()) - amount;
//@ signals (InsufficientBalanceException e) amount > getBalance() + overdraftLimit;
public void withdraw(double amount) throws InsufficientBalanceException {
    if (amount <= 0) {
        throw new ValidationException("Amount must be positive");
    }
    
    double availableBalance = getBalance() + overdraftLimit;
    
    if (amount > availableBalance) {
        throw new InsufficientBalanceException(
            "Insufficient balance. Available: $" + availableBalance
        );
    }
    
    setBalance(getBalance() - amount);
}
```

**Explanation:**
- `requires` - Preconditions that must be true before execution
- `ensures` - Postconditions guaranteed after successful execution
- `signals` - Specifies when exceptions are thrown
- `\old()` - References the previous value of a variable

### Verification Tools

To verify JML specifications, you can use:

- **OpenJML** - Static checker for JML
- **KeY** - Theorem prover for Java+JML
- **ESC/Java2** - Extended Static Checker

```bash
# Example verification with OpenJML (when configured)
openjml -check src/Conta.java
```

### JML Status in this Project

> ⚠️ **In Development:** JML specifications are being refined and may contain inconsistencies. The goal is to demonstrate knowledge of the technique and intention to create formally verifiable software.

**Next Steps:**
- [ ] Add complete JML specifications to all classes
- [ ] Configure OpenJML for automatic verification
- [ ] Fix inconsistencies in existing specifications
- [ ] Add complete class invariants
- [ ] Document test cases based on contracts

---

## 🧪 Exception Handling

### Exception Hierarchy

```
Exception
   │
   ├─ ValidacaoException (ValidationException)
   │  └─ Business validation errors
   │
   └─ SaldoInsuficienteException (InsufficientBalanceException)
      └─ Insufficient balance for operation
```

### Handling Examples

```java
try {
    banco.realizarSaque(accountNumber, 1000.00);
} catch (SaldoInsuficienteException e) {
    System.err.println("❌ " + e.getMessage());
    // Insufficient balance. Available: $500.00
} catch (ValidacaoException e) {
    System.err.println("⚠️ " + e.getMessage());
    // Withdrawal amount must be positive
}
```

### Implemented Validations

- ✅ Unique CPF in registration
- ✅ Positive values in operations
- ✅ Sufficient balance for withdrawals
- ✅ Existing accounts in transfers
- ✅ Credit limit in loans
- ✅ Waiting period in investments
- ✅ Valid installments in loans
- ✅ Required data in registration

---

## 📊 Diagrams

### Transfer Flow

```
┌─────────────┐
│   Customer  │
│  requests   │
│  transfer   │
└──────┬──────┘
       │
       ▼
┌─────────────────────────────────┐
│      BankingService             │
│  performTransfer()              │
└──────┬──────────────────────────┘
       │
       ├─── 1. Validate accounts
       │
       ├─── 2. Withdraw from source
       │         │
       │         ├─ Check balance
       │         └─ Deduct amount
       │
       ├─── 3. Deposit to destination
       │         │
       │         └─ Add amount
       │
       ├─── 4. Record transaction
       │         │
       │         └─ AuditSystem
       │
       └─── 5. If error → Rollback
```

### Investment Lifecycle

```
┌──────────────┐
│  APPLICATION │  ← Customer invests amount
└──────┬───────┘
       │
       ▼
┌──────────────┐
│    ACTIVE    │  ← Daily yield calculation
│  (Locked)    │    Cannot redeem
└──────┬───────┘
       │
       │ After waiting period
       │
       ▼
┌──────────────┐
│    ACTIVE    │  ← Can redeem anytime
│ (Available)  │    Yield continues
└──────┬───────┘
       │
       │ Customer requests redemption
       │
       ▼
┌──────────────┐
│   REDEEMED   │  ← Amount + yield returns to account
└──────────────┘
```

---

## 🔧 Technologies and Concepts

### Technologies

- ☕ **Java 11+** - Main language
- 📝 **JML** - Formal specifications
- 🧪 **Exceptions** - Robust error handling
- 📦 **Collections Framework** - Data management

### Applied Concepts

#### Object-Oriented Programming
- ✅ Encapsulation
- ✅ Inheritance
- ✅ Polymorphism
- ✅ Abstraction
- ✅ Abstract classes and interfaces

#### SOLID Principles
- **S** - Single Responsibility: Each class has a clear responsibility
- **O** - Open/Closed: Extensible without modifying existing code
- **L** - Liskov Substitution: Subtypes can replace base types
- **I** - Interface Segregation: Specific and cohesive interfaces
- **D** - Dependency Inversion: Depends on abstractions, not implementations

#### Best Practices
- 📋 Input validation
- 🔒 Data encapsulation
- 🎯 Cohesive methods with single purpose
- 📝 Documentation via JML
- ⚠️ Appropriate exception handling
- 🔄 Immutability where appropriate

---

## 📈 Future Improvements

### Short Term
- [ ] Complete JML specifications in all classes
- [ ] Add unit tests with JUnit
- [ ] Implement data persistence (database)
- [ ] Create graphical interface (JavaFX or Swing)

### Medium Term
- [ ] REST API with Spring Boot
- [ ] Authentication and authorization
- [ ] PDF reports
- [ ] Email/SMS notifications
- [ ] Administrative dashboard

### Long Term
- [ ] Integration with real banking APIs
- [ ] PIX payment system (Brazilian instant payment)
- [ ] Mobile app (Android/iOS)
- [ ] Credit analysis with Machine Learning
- [ ] Blockchain for audit

---

## 🤝 Contributing

Contributions are welcome! If you want to improve this project:

1. Fork the project
2. Create a branch for your feature (`git checkout -b feature/MyFeature`)
3. Commit your changes (`git commit -m 'Add new feature'`)
4. Push to the branch (`git push origin feature/MyFeature`)
5. Open a Pull Request

### Areas that need help
- 📝 Complete JML specifications
- 🧪 Add unit tests
- 📚 Improve documentation
- 🐛 Report and fix bugs
- ✨ Suggest new features

---

## 📄 License

This project is under the MIT license. See the [LICENSE](LICENSE) file for more details.

---

## 👨‍💻 Author

**Your Name**

- GitHub: [@your-username](https://github.com/your-username)
- LinkedIn: www.linkedin.com/in/joão-guilhermmy-93661b29b
- Email: joaoguilhermmy2@gmail.com

---

## 🙏 Acknowledgments

- Java community for excellent documentation
- OpenJML project for formal verification resources
- Everyone who contributed with ideas and suggestions

---

<div align="center">

### ⭐ If this project was useful, consider giving it a star!

**Developed with ❤️ and lots of ☕**

</div>
