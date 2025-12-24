public abstract class Pessoa {

    private /*@ spec_public @*/ String nome;
    private /*@ spec_public @*/ String cpf;
    private /*@ spec_public @*/ String endereco;
    private /*@ spec_public @*/ String telefone;

    //@ public invariant nome != null && !nome.isEmpty();
    //@ public invariant cpf != null && cpf.length() == 11;
    //@ public invariant endereco != null;
    //@ public invariant telefone != null && telefone.length() >= 8 && telefone.length() <= 13;

    //@ requires n != null && !n.isEmpty();
    //@ requires c != null && c.length() == 11;
    //@ requires end != null;
    //@ requires tel != null && tel.length() >= 8 && tel.length() <= 13;
    //@ ensures this.nome.equals(n);
    //@ ensures this.cpf.equals(c);
    //@ ensures this.endereco.equals(end);
    //@ ensures this.telefone.equals(tel);
    //@ pure
    public Pessoa(String n, String c, String end, String tel) {
        this.nome = n;
        this.cpf = c;
        this.endereco = end;
        this.telefone = tel;
    }

    //@ ensures \result != null && !\result.isEmpty();
    //@ ensures \result.equals(nome);
    public /*@ pure @*/ String getNome() {
        return nome;
    }

    //@ requires n != null && !n.isEmpty();
    //@ assignable nome;
    //@ ensures nome.equals(n);
    public void setNome(String n) {
        this.nome = n;
    }

    //@ ensures \result != null && \result.length() == 11;
    //@ ensures \result.equals(cpf);
    //@ pure
    public String getCpf() {
        return cpf;
    }

    //@ requires c != null && c.length() == 11;
    //@ assignable cpf;
    //@ ensures cpf.equals(c);
    public void setCpf(String c) {
        this.cpf = c;
    }

    //@ ensures \result != null;
    //@ ensures \result.equals(endereco);
    //@ pure
    public String getEndereco() {
        return endereco;
    }

    //@ requires end != null;
    //@ assignable endereco;
    //@ ensures endereco.equals(end);
    public void setEndereco(String end) {
        this.endereco = end;
    }

    //@ ensures \result != null && \result.length() >= 8 && \result.length() <= 13;
    //@ ensures \result.equals(telefone);
    //@ pure
    public String getTelefone() {
        return telefone;
    }

    //@ requires tel != null && tel.length() >= 8 && tel.length() <= 13;
    //@ assignable telefone;
    //@ ensures telefone.equals(tel);
    public void setTelefone(String tel) {
        this.telefone = tel;
    }

    //@ ensures \result != null;
    //@ pure
    public abstract String getDescricao();
}
