import React, { useState } from 'react';
import { Github, Star, GitFork, Download, Code, Users, Shield, TrendingUp, FileText, CheckCircle, AlertTriangle, BookOpen, Terminal, Zap, Lock, Database, Activity } from 'lucide-react';

const BancoReadme = () => {
  const [activeTab, setActiveTab] = useState('overview');
  const [copiedCode, setCopiedCode] = useState('');

  const copyToClipboard = (code, id) => {
    navigator.clipboard.writeText(code);
    setCopiedCode(id);
    setTimeout(() => setCopiedCode(''), 2000);
  };

  const tabs = [
    { id: 'overview', label: 'Visão Geral', icon: BookOpen },
    { id: 'features', label: 'Funcionalidades', icon: Zap },
    { id: 'architecture', label: 'Arquitetura', icon: Database },
    { id: 'installation', label: 'Instalação', icon: Download },
    { id: 'usage', label: 'Como Usar', icon: Terminal },
    { id: 'jml', label: 'JML & Qualidade', icon: Shield },
  ];

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-900 via-blue-900 to-slate-900 text-white">
      {/* Header */}
      <header className="border-b border-blue-800/30 bg-black/20 backdrop-blur-sm sticky top-0 z-50">
        <div className="max-w-7xl mx-auto px-6 py-6">
          <div className="flex items-center justify-between">
            <div className="flex items-center gap-4">
              <div className="w-14 h-14 bg-gradient-to-br from-blue-400 to-blue-600 rounded-xl flex items-center justify-center shadow-lg shadow-blue-500/50">
                <Database className="w-8 h-8" />
              </div>
              <div>
                <h1 className="text-3xl font-bold bg-gradient-to-r from-blue-400 to-cyan-400 bg-clip-text text-transparent">
                  Sistema Bancário Java
                </h1>
                <p className="text-gray-400 text-sm mt-1">Sistema completo com JML Annotations</p>
              </div>
            </div>
            <div className="flex gap-3">
              <button className="flex items-center gap-2 px-4 py-2 bg-blue-600 hover:bg-blue-700 rounded-lg transition-colors">
                <Star className="w-4 h-4" />
                <span>Star</span>
              </button>
              <button className="flex items-center gap-2 px-4 py-2 bg-slate-700 hover:bg-slate-600 rounded-lg transition-colors">
                <GitFork className="w-4 h-4" />
                <span>Fork</span>
              </button>
            </div>
          </div>
        </div>
      </header>

      {/* Navigation Tabs */}
      <nav className="border-b border-blue-800/30 bg-black/10 backdrop-blur-sm sticky top-24 z-40">
        <div className="max-w-7xl mx-auto px-6">
          <div className="flex gap-1 overflow-x-auto">
            {tabs.map((tab) => {
              const Icon = tab.icon;
              return (
                <button
                  key={tab.id}
                  onClick={() => setActiveTab(tab.id)}
                  className={`flex items-center gap-2 px-5 py-3 border-b-2 transition-all whitespace-nowrap ${
                    activeTab === tab.id
                      ? 'border-blue-500 text-blue-400 bg-blue-500/10'
                      : 'border-transparent text-gray-400 hover:text-gray-300 hover:bg-white/5'
                  }`}
                >
                  <Icon className="w-4 h-4" />
                  {tab.label}
                </button>
              );
            })}
          </div>
        </div>
      </nav>

      {/* Content */}
      <main className="max-w-7xl mx-auto px-6 py-12">
        {/* Overview Tab */}
        {activeTab === 'overview' && (
          <div className="space-y-12 animate-fadeIn">
            {/* Hero Section */}
            <div className="text-center space-y-6">
              <div className="inline-flex items-center gap-2 px-4 py-2 bg-blue-500/10 border border-blue-500/30 rounded-full text-blue-400 text-sm">
                <Activity className="w-4 h-4" />
                Sistema em Desenvolvimento • JML Annotations
              </div>
              <h2 className="text-5xl font-bold">
                Sistema Bancário Completo
              </h2>
              <p className="text-xl text-gray-400 max-w-3xl mx-auto">
                Aplicação robusta em Java com anotações JML para garantir confiabilidade e qualidade de código. 
                Demonstrando práticas avançadas de programação orientada a objetos e design de software.
              </p>
            </div>

            {/* Stats */}
            <div className="grid grid-cols-2 md:grid-cols-4 gap-6">
              {[
                { icon: Code, label: 'Linhas de Código', value: '2000+' },
                { icon: FileText, label: 'Classes Java', value: '18' },
                { icon: Shield, label: 'JML Specs', value: 'Em Progresso' },
                { icon: CheckCircle, label: 'Cobertura', value: 'Alta' },
              ].map((stat, i) => {
                const Icon = stat.icon;
                return (
                  <div key={i} className="bg-gradient-to-br from-slate-800/50 to-blue-900/30 border border-blue-700/30 rounded-xl p-6 text-center">
                    <Icon className="w-8 h-8 mx-auto mb-3 text-blue-400" />
                    <div className="text-3xl font-bold text-white mb-1">{stat.value}</div>
                    <div className="text-sm text-gray-400">{stat.label}</div>
                  </div>
                );
              })}
            </div>

            {/* Key Highlights */}
            <div className="bg-gradient-to-br from-slate-800/50 to-blue-900/30 border border-blue-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-6 flex items-center gap-3">
                <Star className="w-6 h-6 text-yellow-400" />
                Destaques do Projeto
              </h3>
              <div className="grid md:grid-cols-2 gap-6">
                {[
                  {
                    title: 'Arquitetura Orientada a Objetos',
                    desc: 'Design patterns e princípios SOLID implementados',
                    icon: Database,
                  },
                  {
                    title: 'Sistema de Auditoria Integrado',
                    desc: 'Rastreamento completo de todas as transações',
                    icon: Activity,
                  },
                  {
                    title: 'Múltiplos Tipos de Conta',
                    desc: 'Corrente, Poupança e Investimento com lógicas específicas',
                    icon: TrendingUp,
                  },
                  {
                    title: 'Validações Robustas',
                    desc: 'Sistema de exceções customizado para garantir integridade',
                    icon: Shield,
                  },
                ].map((item, i) => {
                  const Icon = item.icon;
                  return (
                    <div key={i} className="flex gap-4">
                      <div className="w-12 h-12 bg-blue-500/20 rounded-lg flex items-center justify-center flex-shrink-0">
                        <Icon className="w-6 h-6 text-blue-400" />
                      </div>
                      <div>
                        <h4 className="font-semibold text-lg mb-1">{item.title}</h4>
                        <p className="text-gray-400 text-sm">{item.desc}</p>
                      </div>
                    </div>
                  );
                })}
              </div>
            </div>

            {/* About JML */}
            <div className="bg-gradient-to-r from-amber-900/20 to-orange-900/20 border border-amber-700/30 rounded-2xl p-8">
              <div className="flex items-start gap-4">
                <AlertTriangle className="w-8 h-8 text-amber-400 flex-shrink-0 mt-1" />
                <div>
                  <h3 className="text-2xl font-bold mb-3 text-amber-400">Sobre as Anotações JML</h3>
                  <p className="text-gray-300 mb-4">
                    Este projeto inclui anotações <strong>JML (Java Modeling Language)</strong> para especificações formais 
                    de comportamento. As anotações JML estão em fase de desenvolvimento e demonstram a intenção de criar 
                    código com <strong>mínimo de erros possíveis</strong> através de contratos formais.
                  </p>
                  <p className="text-gray-400 text-sm">
                    <strong>Nota:</strong> Algumas especificações JML podem apresentar inconsistências e estão sendo refinadas. 
                    O foco principal é demonstrar conhecimento em técnicas avançadas de verificação de software.
                  </p>
                </div>
              </div>
            </div>
          </div>
        )}

        {/* Features Tab */}
        {activeTab === 'features' && (
          <div className="space-y-8 animate-fadeIn">
            <h2 className="text-4xl font-bold mb-8">Funcionalidades Principais</h2>
            
            <div className="grid md:grid-cols-2 gap-6">
              {[
                {
                  title: 'Gestão de Clientes',
                  items: ['Cadastro completo com validação de CPF', 'Categorias: Comum e Premium', 'Cálculo automático de limite de crédito', 'Histórico de transações'],
                  color: 'blue',
                },
                {
                  title: 'Contas Bancárias',
                  items: ['Conta Corrente com cheque especial', 'Conta Poupança com rendimento', 'Conta Investimento com carteira', 'Geração automática de números únicos'],
                  color: 'green',
                },
                {
                  title: 'Operações Financeiras',
                  items: ['Depósitos e saques validados', 'Transferências entre contas', 'Sistema de tarifas diferenciadas', 'Controle de saldo em tempo real'],
                  color: 'purple',
                },
                {
                  title: 'Empréstimos',
                  items: ['Cálculo de juros compostos', 'Parcelamento configurável', 'Controle de limite de crédito', 'Sistema de multas por atraso'],
                  color: 'red',
                },
                {
                  title: 'Investimentos',
                  items: ['CDB, Tesouro Direto, LCI, LCA, Fundos', 'Rentabilidade automática', 'Período de carência respeitado', 'Resgate com cálculo de rendimento'],
                  color: 'cyan',
                },
                {
                  title: 'Auditoria & Compliance',
                  items: ['Log completo de transações', 'Detecção de operações suspeitas', 'Alertas para valores elevados', 'Conformidade automatizada'],
                  color: 'amber',
                },
              ].map((feature, i) => (
                <div key={i} className={`bg-gradient-to-br from-slate-800/50 to-${feature.color}-900/30 border border-${feature.color}-700/30 rounded-xl p-6`}>
                  <h3 className="text-xl font-bold mb-4 flex items-center gap-2">
                    <CheckCircle className={`w-5 h-5 text-${feature.color}-400`} />
                    {feature.title}
                  </h3>
                  <ul className="space-y-2">
                    {feature.items.map((item, j) => (
                      <li key={j} className="flex items-start gap-2 text-gray-300 text-sm">
                        <span className={`w-1.5 h-1.5 bg-${feature.color}-400 rounded-full mt-2 flex-shrink-0`}></span>
                        {item}
                      </li>
                    ))}
                  </ul>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* Architecture Tab */}
        {activeTab === 'architecture' && (
          <div className="space-y-8 animate-fadeIn">
            <h2 className="text-4xl font-bold mb-8">Arquitetura do Sistema</h2>

            {/* Class Diagram */}
            <div className="bg-gradient-to-br from-slate-800/50 to-blue-900/30 border border-blue-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-6">Diagrama de Classes</h3>
              <div className="bg-slate-900/50 rounded-lg p-6 overflow-x-auto">
                <pre className="text-sm text-gray-300">
{`┌─────────────────┐
│     Pessoa      │ (Abstract)
├─────────────────┤
│ - nome          │
│ - cpf           │
│ - endereco      │
│ - telefone      │
└────────┬────────┘
         │
    ┌────┴────┐
    │         │
┌───▼────┐ ┌─▼───────────┐
│Cliente │ │ Funcionario │
├────────┤ ├─────────────┤
│ - id   │ │ - matricula │
│ - tipo │ │ - cargo     │
│ - renda│ │ - salario   │
└───┬────┘ └─────────────┘
    │
    │ 1..*
    │
┌───▼──────────┐
│    Conta     │ (Abstract)
├──────────────┤
│ - numero     │
│ - saldo      │
│ - titular    │
└──────┬───────┘
       │
  ┌────┼────┬──────────┐
  │    │    │          │
┌─▼──┐ │ ┌──▼──────┐ ┌▼──────────┐
│ CC │ │ │  CP     │ │    CI     │
└────┘ │ └─────────┘ └───────────┘
       │
    ┌──▼──────────┐
    │ BancoService│
    ├─────────────┤
    │ + criar()   │
    │ + listar()  │
    │ + operar()  │
    └─────────────┘`}
                </pre>
              </div>
            </div>

            {/* Design Patterns */}
            <div className="grid md:grid-cols-3 gap-6">
              {[
                {
                  pattern: 'Service Layer',
                  desc: 'BancoService centraliza toda lógica de negócio',
                  icon: Database,
                },
                {
                  pattern: 'Factory Method',
                  desc: 'Criação de diferentes tipos de conta',
                  icon: Code,
                },
                {
                  pattern: 'Strategy',
                  desc: 'Cálculo de tarifas por tipo de conta',
                  icon: TrendingUp,
                },
              ].map((item, i) => {
                const Icon = item.icon;
                return (
                  <div key={i} className="bg-gradient-to-br from-slate-800/50 to-purple-900/30 border border-purple-700/30 rounded-xl p-6">
                    <Icon className="w-8 h-8 text-purple-400 mb-3" />
                    <h4 className="font-bold text-lg mb-2">{item.pattern}</h4>
                    <p className="text-gray-400 text-sm">{item.desc}</p>
                  </div>
                );
              })}
            </div>

            {/* Key Classes */}
            <div className="bg-gradient-to-br from-slate-800/50 to-blue-900/30 border border-blue-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-6">Classes Principais</h3>
              <div className="grid md:grid-cols-2 gap-4">
                {[
                  { name: 'BancoService', desc: 'Orquestra todas as operações do sistema' },
                  { name: 'Cliente / Funcionario', desc: 'Hierarquia de pessoas no sistema' },
                  { name: 'Conta (Abstract)', desc: 'Base para todos os tipos de conta' },
                  { name: 'Emprestimo', desc: 'Gestão completa de empréstimos' },
                  { name: 'Investimento', desc: 'Produtos de investimento com rentabilidade' },
                  { name: 'SistemaAuditoria', desc: 'Rastreamento e alertas de segurança' },
                  { name: 'Transacao', desc: 'Registro imutável de operações' },
                  { name: 'ValidacaoException', desc: 'Tratamento customizado de erros' },
                ].map((cls, i) => (
                  <div key={i} className="flex items-start gap-3 bg-slate-900/50 rounded-lg p-4">
                    <Code className="w-5 h-5 text-blue-400 flex-shrink-0 mt-0.5" />
                    <div>
                      <div className="font-mono text-blue-400 font-semibold">{cls.name}</div>
                      <div className="text-gray-400 text-sm mt-1">{cls.desc}</div>
                    </div>
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/* Installation Tab */}
        {activeTab === 'installation' && (
          <div className="space-y-8 animate-fadeIn">
            <h2 className="text-4xl font-bold mb-8">Instalação e Configuração</h2>

            {/* Prerequisites */}
            <div className="bg-gradient-to-br from-slate-800/50 to-blue-900/30 border border-blue-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-6">Pré-requisitos</h3>
              <div className="space-y-4">
                {[
                  { name: 'Java Development Kit', version: '11 ou superior', icon: '☕' },
                  { name: 'IDE', version: 'IntelliJ IDEA, Eclipse ou VS Code', icon: '🛠️' },
                  { name: 'Git', version: 'Para clonar o repositório', icon: '📦' },
                ].map((req, i) => (
                  <div key={i} className="flex items-center gap-4 bg-slate-900/50 rounded-lg p-4">
                    <span className="text-3xl">{req.icon}</span>
                    <div>
                      <div className="font-semibold">{req.name}</div>
                      <div className="text-gray-400 text-sm">{req.version}</div>
                    </div>
                  </div>
                ))}
              </div>
            </div>

            {/* Installation Steps */}
            <div className="space-y-6">
              <h3 className="text-2xl font-bold">Passos de Instalação</h3>
              
              {[
                {
                  step: '1',
                  title: 'Clone o repositório',
                  code: 'git clone https://github.com/seu-usuario/sistema-bancario-java.git\ncd sistema-bancario-java',
                  id: 'clone',
                },
                {
                  step: '2',
                  title: 'Compile o projeto',
                  code: 'javac -d bin src/*.java',
                  id: 'compile',
                },
                {
                  step: '3',
                  title: 'Execute a aplicação',
                  code: 'java -cp bin Main',
                  id: 'run',
                },
              ].map((item, i) => (
                <div key={i} className="bg-gradient-to-br from-slate-800/50 to-green-900/30 border border-green-700/30 rounded-xl overflow-hidden">
                  <div className="bg-green-900/30 px-6 py-3 border-b border-green-700/30">
                    <div className="flex items-center gap-3">
                      <div className="w-8 h-8 bg-green-500 rounded-full flex items-center justify-center font-bold">
                        {item.step}
                      </div>
                      <h4 className="font-semibold text-lg">{item.title}</h4>
                    </div>
                  </div>
                  <div className="p-6">
                    <div className="relative">
                      <pre className="bg-slate-900 rounded-lg p-4 overflow-x-auto">
                        <code className="text-sm text-green-400">{item.code}</code>
                      </pre>
                      <button
                        onClick={() => copyToClipboard(item.code, item.id)}
                        className="absolute top-2 right-2 px-3 py-1 bg-slate-700 hover:bg-slate-600 rounded text-xs transition-colors"
                      >
                        {copiedCode === item.id ? '✓ Copiado!' : 'Copiar'}
                      </button>
                    </div>
                  </div>
                </div>
              ))}
            </div>

            {/* Using IDE */}
            <div className="bg-gradient-to-br from-slate-800/50 to-purple-900/30 border border-purple-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-4">Usando uma IDE</h3>
              <div className="space-y-3 text-gray-300">
                <p><strong>IntelliJ IDEA / Eclipse:</strong></p>
                <ol className="list-decimal list-inside space-y-2 ml-4">
                  <li>Abra a IDE e selecione "Import Project" ou "Open"</li>
                  <li>Navegue até a pasta do projeto clonado</li>
                  <li>A IDE detectará automaticamente os arquivos Java</li>
                  <li>Localize a classe <code className="bg-slate-900 px-2 py-1 rounded text-blue-400">Main.java</code></li>
                  <li>Clique com botão direito → "Run 'Main.main()'"</li>
                </ol>
              </div>
            </div>
          </div>
        )}

        {/* Usage Tab */}
        {activeTab === 'usage' && (
          <div className="space-y-8 animate-fadeIn">
            <h2 className="text-4xl font-bold mb-8">Como Usar o Sistema</h2>

            {/* Quick Start */}
            <div className="bg-gradient-to-br from-slate-800/50 to-cyan-900/30 border border-cyan-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-6">Início Rápido</h3>
              <p className="text-gray-300 mb-6">
                O sistema oferece um menu interativo completo no terminal. Após iniciar a aplicação, 
                você terá acesso a 24 opções organizadas por categoria.
              </p>
              
              <div className="bg-slate-900/50 rounded-lg p-6">
                <div className="font-mono text-sm text-green-400">
                  <div>=== PAINEL DE CONTROLE DO BANCO ===</div>
                  <div className="mt-2 text-gray-400">--- Clientes ---</div>
                  <div>1. Cadastrar Cliente</div>
                  <div>2. Listar Clientes</div>
                  <div className="mt-2 text-gray-400">--- Contas ---</div>
                  <div>5. Criar Conta Corrente</div>
                  <div>6. Criar Conta Poupança</div>
                  <div className="mt-2 text-gray-400">--- Operações Básicas ---</div>
                  <div>10. Realizar Depósito</div>
                  <div>11. Realizar Saque</div>
                  <div>12. Realizar Transferência</div>
                  <div className="mt-2">...</div>
                </div>
              </div>
            </div>

            {/* Usage Examples */}
            <div className="space-y-6">
              <h3 className="text-2xl font-bold">Exemplos de Uso</h3>

              {[
                {
                  title: 'Cadastrar um Cliente',
                  steps: [
                    'Selecione a opção 1 no menu',
                    'Informe: Nome, CPF, Endereço, Telefone',
                    'Escolha o tipo: "comum" ou "premium"',
                    'Informe a renda mensal',
                    'O sistema calculará automaticamente o limite de crédito',
                  ],
                  color: 'blue',
                },
                {
                  title: 'Criar uma Conta Corrente',
                  steps: [
                    'Selecione a opção 5',
                    'Digite o CPF do cliente cadastrado',
                    'Defina o limite do cheque especial',
                    'Um número de conta único será gerado',
                  ],
                  color: 'green',
                },
                {
                  title: 'Realizar um Investimento',
                  steps: [
                    'Crie uma Conta Investimento (opção 7)',
                    'Deposite um valor inicial (opção 10)',
                    'Escolha a opção 14 para investir',
                    'Selecione: CDB, Tesouro Direto, LCI, LCA ou Fundo',
                    'O rendimento será calculado automaticamente',
                  ],
                  color: 'purple',
                },
                {
                  title: 'Contratar um Empréstimo',
                  steps: [
                    'Selecione a opção 16',
                    'Informe o CPF do cliente',
                    'Digite o valor desejado (limitado ao crédito disponível)',
                    'Defina o número de parcelas e taxa de juros',
                    'Use a opção 17 para pagar as parcelas',
                  ],
                  color: 'red',
                },
              ].map((example, i) => (
                <div key={i} className={`bg-gradient-to-br from-slate-800/50 to-${example.color}-900/30 border border-${example.color}-700/30 rounded-xl p-6`}>
                  <h4 className="text-xl font-bold mb-4 flex items-center gap-2">
                    <Terminal className={`w-5 h-5 text-${example.color}-400`} />
                    {example.title}
                  </h4>
                  <ol className="space-y-2">
                    {example.steps.map((step, j) => (
                      <li key={j} className="flex gap-3 text-gray-300">
                        <span className={`w-6 h-6 bg-${example.color}-500/20 text-${example.color}-400 rounded-full flex items-center justify-center flex-shrink-0 text-sm font-semibold`}>
                          {j + 1}
                        </span>
                        <span className="pt-0.5">{step}</span>
                      </li>
                    ))}
                  </ol>
                </div>
              ))}
            </div>

            {/* Code Example */}
            <div className="bg-gradient-to-br from-slate-800/50 to-amber-900/30 border border-amber-700/30 rounded-2xl p-8">
              <h3 className="text-2xl font-bold mb-6">Exemplo de Código</h3>
              <p className="text-gray-300 mb-4">Como usar a classe BancoService programaticamente:</p>
              <div className="relative">
                <pre className="bg-slate-900 rounded-lg p-6 overflow-x-auto">
                  <code className="text-sm text-gray-300">{`BancoService banco = new BancoService();

// Cadastrar cliente
Cliente cliente = banco.cadastrarCliente(
    "João Silva", 
    "123.456.789-00",
    "Rua A, 123",
    "83999887766",
    "premium",
    5000.00
);

// Criar conta corrente
Conta conta = banco.criarContaCorrente(
    "123.456.789-00", 
    1000.00
);

// Realizar depósito
banco.realizarDeposito(conta.getNumero(), 500.00);

// Consultar saldo
System.out.println("Saldo: R$ " + conta.getSaldo());`}</code>
                </pre>
                <button
                  onClick={() => copyToClipboard(`BancoService banco = new BancoService();

// Cadastrar cliente
Cliente cliente = banco.cadastrarCliente(
    "João Silva", 
    "123.456.789-00",
    "Rua A, 123",
    "83999887766",
    "premium",
    5000
