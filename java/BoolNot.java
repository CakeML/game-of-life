import java.util.*;

public class BoolNot implements BoolExp {

    private BoolExp e1;

    public static BoolExp make(BoolExp e1) {
        // ~T --> F
        if (e1 instanceof BoolTrue) { return new BoolFalse(); }
        // ~F --> e2
        if (e1 instanceof BoolFalse) { return new BoolTrue(); }
        // ~~x --> x
        if (e1 instanceof BoolNot) { return ((BoolNot)e1).e1; }
        return new BoolNot(e1);
    }

    private BoolNot(BoolExp e1) {
        this.e1 = e1;
    }

    public boolean eval(Map<String,Boolean> m) {
        return !e1.eval(m);
    }

    public void addVars(Set<String> m) {
        e1.addVars(m);
    }

    public String toString() {
        return "(~" + e1.toString() + ")";
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        if (o instanceof BoolNot) {
            BoolNot other = (BoolNot)o;
            return other.e1.equals(this.e1);
        } else { return false; }
    }

}
