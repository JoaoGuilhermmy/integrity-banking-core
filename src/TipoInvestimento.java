public enum TipoInvestimento {
    CDB(0.8, 90),
    TESOURO_DIRETO(0.6, 180),
    LCI(0.7, 90),
    LCA(0.7, 90),
    FUNDO_RENDA_FIXA(0.5, 30);

    private /*@ spec_public @*/ final double taxaMensal;
    private /*@ spec_public @*/ final int diasCarencia;

    //@ public invariant taxaMensal > 0;
    //@ public invariant diasCarencia > 0;

    //@ requires taxa > 0;
    //@ requires dias > 0;
    //@ ensures this.taxaMensal == taxa;
    //@ ensures this.diasCarencia == dias;
    TipoInvestimento(double taxa, int dias) {
        this.taxaMensal = taxa;
        this.diasCarencia = dias;
    }

    //@ ensures \result == taxaMensal;
    //@ ensures \result > 0;
    //@ pure
    public double getTaxaMensal() {
        return taxaMensal;
    }

    //@ ensures \result == diasCarencia;
    //@ ensures \result > 0;
    //@ pure
    public int getDiasCarencia() {
        return diasCarencia;
    }
}
