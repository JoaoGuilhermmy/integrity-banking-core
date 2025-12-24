public class Funcionario extends Pessoa {

    private /*@ spec_public @*/ int matricula;
    private /*@ spec_public @*/ String cargo;
    private /*@ spec_public @*/ double salario;

    //@ public invariant matricula > 0;
    //@ public invariant cargo != null && !cargo.isEmpty();
    //@ public invariant salario > 0;

    //@ requires nome != null && !nome.isEmpty();
    //@ requires cpf != null && cpf.length() == 11;
    //@ requires endereco != null;
    //@ requires telefone != null && telefone.length() >= 8 && telefone.length() <= 13;
    //@ requires mat > 0;
    //@ requires c != null && !c.isEmpty();
    //@ requires sal > 0;
    //@ ensures this.matricula == mat;
    //@ ensures this.cargo.equals(c);
    //@ ensures this.salario == sal;
    //@ pure
    public Funcionario(String nome, String cpf, String endereco, String telefone,
                       int mat, String c, double sal) {
        super(nome, cpf, endereco, telefone);
        this.matricula = mat;
        this.cargo = c;
        this.salario = sal;
    }

    //@ ensures \result == matricula;
    //@ ensures \result > 0;
    //@ pure
    public int getMatricula() {
        return matricula;
    }

    //@ requires mat > 0;
    //@ assignable matricula;
    //@ ensures matricula == mat;
    public void setMatricula(int mat) {
        this.matricula = mat;
    }

    //@ ensures \result != null && !\result.isEmpty();
    //@ ensures \result.equals(cargo);
    //@ pure
    public String getCargo() {
        return cargo;
    }

    //@ requires c != null && !c.isEmpty();
    //@ assignable cargo;
    //@ ensures cargo.equals(c);
    public void setCargo(String c) {
        this.cargo = c;
    }

    //@ ensures \result == salario;
    //@ ensures \result > 0;
    //@ pure
    public double getSalario() {
        return salario;
    }

    //@ requires sal > 0;
    //@ assignable salario;
    //@ ensures salario == sal;
    public void setSalario(double sal) {
        this.salario = sal;
    }

    //@ ensures \result == salario * 0.10;
    //@ ensures \result >= 0;
    //@ pure
    public double calcularBonificacao() {
        return this.salario * 0.10;
    }

    //@ also
    //@ ensures \result != null;
    //@ ensures \result.contains(cargo);
    //@ ensures \result.contains(getNome());
    //@ pure
    public String getDescricao() {
        return "Funcionário (" + this.cargo + ") - " + this.getNome();
    }
}
