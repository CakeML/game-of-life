import java.util.*;

public interface BoolExp {

    public boolean eval(Map<String,Boolean> m);

    public void addVars(Set<String> m);

}
