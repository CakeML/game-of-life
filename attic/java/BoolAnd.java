import java.util.*;

public class BoolAnd implements BoolExp {

    private BoolExp e1;
    private BoolExp e2;

    public static BoolExp make(BoolExp e1, BoolExp e2) {
        // T /\ e2 --> e2
        if (e1 instanceof BoolTrue) { return e2; }
        // F /\ e2 --> F
        if (e1 instanceof BoolFalse) { return new BoolFalse(); }
        // e1 /\ T --> e1
        if (e2 instanceof BoolTrue) { return e1; }
        // e1 /\ F --> F
        if (e2 instanceof BoolFalse) { return new BoolFalse(); }
        return new BoolAnd(e1,e2);
    }

    private BoolAnd(BoolExp e1, BoolExp e2) {
        this.e1 = e1;
        this.e2 = e2;
    }

    public boolean eval(Map<String,Boolean> m) {
        return e1.eval(m) && e2.eval(m);
    }

    public void addVars(Set<String> m) {
        e1.addVars(m);
        e2.addVars(m);
    }

    public String toString() {
        return "(" + e1.toString() + " ∧ " + e2.toString() + ")";
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        if (o instanceof BoolAnd) {
            BoolAnd other = (BoolAnd)o;
            return other.e1.equals(this.e1) &&
                   other.e2.equals(this.e2);
        } else { return false; }
    }

}
