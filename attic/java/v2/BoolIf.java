import java.util.*;

public class BoolIf implements BoolExp {

    private BoolExp e0;
    private BoolExp e1;
    private BoolExp e2;

    public static BoolExp make(BoolExp e0, BoolExp e1, BoolExp e2) {
        // if T then e1 else e2 --> e1
        if (e0 instanceof BoolTrue) { return e1; }
        // if F then e1 else e2 --> e2
        if (e0 instanceof BoolFalse) { return e2; }
        // if e0 then e1 else e1 --> e1
        if (e1.equals(e2)) { return e1; }
        // if e0 then F else e2 --> ~e0 /\ e2
        if (e1 instanceof BoolFalse) {
            return BoolAnd.make(BoolNot.make(e0),e2);
        }
        // if e0 then e1 else F --> e0 /\ e1
        if (e2 instanceof BoolFalse) {
            return BoolAnd.make(e0,e1);
        }
        // if e0 then e1 else T --> ~e0 \/ e1
        if (e2 instanceof BoolTrue) {
            return BoolOr.make(BoolNot.make(e0),e1);
        }
        // if e0 then T else e2 --> e0 \/ e2
        if (e1 instanceof BoolTrue) {
            return BoolOr.make(e0,e2);
        }
        return new BoolIf(e0,e1,e2);
    }

    private BoolIf(BoolExp e0, BoolExp e1, BoolExp e2) {
        this.e0 = e0;
        this.e1 = e1;
        this.e2 = e2;
    }

    public boolean eval(Map<String,Boolean> m) {
        if (e0.eval(m)) {
            return e1.eval(m);
        } else {
            return e2.eval(m);
        }
    }

    public void addVars(Set<String> m) {
        e0.addVars(m);
        e1.addVars(m);
        e2.addVars(m);
    }

    public String toString() {
        return "(if " + e0.toString() +
               " then " + e1.toString() +
               " else " + e2.toString() + ")";
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        if (o instanceof BoolIf) {
            BoolIf other = (BoolIf)o;
            return other.e0.equals(this.e0) &&
                   other.e1.equals(this.e1) &&
                   other.e2.equals(this.e2);
        } else { return false; }
    }

}
