import java.util.*;

public class BoolFalse implements BoolExp {

    public boolean eval(Map<String,Boolean> m) {
        return false;
    }

    public void addVars(Set<String> m) { }

    public String toString() {
        return "F";
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        return (o instanceof BoolFalse);
    }

}
