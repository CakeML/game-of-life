import java.util.*;

public class BoolVar implements BoolExp {

    private String name;

    public BoolVar(String name) {
        this.name = name;
    }

    public boolean eval(Map<String,Boolean> m) {
        Boolean b = m.get(name);
        if (b == null) {
            throw new IllegalArgumentException("Bad var name: " + name);
        }
        return b;
    }

    public void addVars(Set<String> m) {
        m.add(name);
    }

    public String toString() {
        return name;
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        if (o instanceof BoolVar) {
            BoolVar other = (BoolVar)o;
            return other.name.equals(this.name);
        } else { return false; }
    }

}
