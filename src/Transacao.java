import java.time.LocalDateTime;

public class Transacao {
    private /*@ spec_public @*/ static int contadorId = 0;

    private /*@ spec_public @*/ int id;
    private /*@ spec_public @*/ TipoTransacao tipo;
    private /*@ spec_public @*/ double valor;
    private /*@ spec_public @*/ LocalDateTime dataHora;
    private /*@ spec_public @*/ /*@ nullable @*/ Conta contaOrigem;
    private /*@ spec_public @*/ /*@ nullable @*/ Conta contaDestino;
    private /*@ spec_public @*/ String descricao;

    //@ public invariant id > 0;
    //@ public invariant tipo != null;
    //@ public invariant valor > 0;
    //@ public invariant dataHora != null;
    //@ public invariant descricao != null;

    //@ requires tipo != null;
    //@ requires valor > 0;
    //@ requires descricao != null;
    //@ ensures this.tipo == tipo;
    //@ ensures this.valor == valor;
    //@ ensures this.descricao.equals(descricao);
    //@ ensures this.id > \old(contadorId);
    //@ ensures this.dataHora != null;
    //@ ensures this.contaOrigem == null;
    //@ ensures this.contaDestino == null;
    public Transacao(TipoTransacao tipo, double valor, String descricao) {
        contadorId++;
        this.id = contadorId;
        this.tipo = tipo;
        this.valor = valor;
        this.dataHora = LocalDateTime.now();
        this.descricao = descricao;
    }

    //@ requires tipo != null;
    //@ requires valor > 0;
    //@ requires descricao != null;
    //@ ensures this.tipo == tipo;
    //@ ensures this.valor == valor;
    //@ ensures this.descricao.equals(descricao);
    //@ ensures this.contaOrigem == origem;
    //@ ensures this.contaDestino == destino;
    //@ ensures this.id > 0;
    //@ ensures this.dataHora != null;
    public Transacao(TipoTransacao tipo, double valor, String descricao,
                     Conta origem, Conta destino) {
        this(tipo, valor, descricao);
        this.contaOrigem = origem;
        this.contaDestino = destino;
    }

    //@ ensures \result == id;
    //@ ensures \result > 0;
    //@ pure
    public int getId() {
        return id;
    }

    //@ ensures \result == tipo;
    //@ ensures \result != null;
    //@ pure
    public TipoTransacao getTipo() {
        return tipo;
    }

    //@ ensures \result == valor;
    //@ ensures \result > 0;
    //@ pure
    public double getValor() {
        return valor;
    }

    //@ ensures \result == dataHora;
    //@ ensures \result != null;
    //@ pure
    public LocalDateTime getDataHora() {
        return dataHora;
    }

    //@ ensures \result == contaOrigem;
    //@ pure
    public /*@ nullable @*/ Conta getContaOrigem() {
        return contaOrigem;
    }

    //@ ensures \result == contaDestino;
    //@ pure
    public /*@ nullable @*/ Conta getContaDestino() {
        return contaDestino;
    }

    //@ ensures \result == descricao;
    //@ ensures \result != null;
    //@ pure
    public String getDescricao() {
        return descricao;
    }

    //@ ensures \result == (valor > 10000);
    //@ pure
    public boolean requerDocumentacao() {
        return valor > 10000;
    }

    //@ also
    //@ ensures \result != null;
    //@ pure
    @Override
    public String toString() {
        return String.format("[ID:%d] %s - R$ %.2f em %s - %s",
                id, tipo, valor, dataHora, descricao);
    }
}
