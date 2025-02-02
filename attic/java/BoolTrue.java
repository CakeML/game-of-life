import java.util.*;

public class BoolTrue implements BoolExp {

    public boolean eval(Map<String,Boolean> m) {
        return true;
    }

    public void addVars(Set<String> m) { }

    public String toString() {
        return "T";
    }

    public boolean equals(Object o) {
        if (o == null) { return false; }
        return (o instanceof BoolTrue);
    }

}
