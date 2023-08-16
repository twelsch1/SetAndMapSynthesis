package variables;

import datatypes.IntData;
import ec.EvolutionState;
import ec.Problem;
import ec.gp.ADFStack;
import ec.gp.GPData;
import ec.gp.GPIndividual;
import ec.gp.GPNode;
import evoSynthesis.CLIAProblem;

@SuppressWarnings("serial")
public class Var17 extends GPNode {

	public String toString() { return "var17;"; }

    public int expectedChildren() { return 0; }
	
    @Override
    public void eval(final EvolutionState state,
            final int thread,
            final GPData input,
            final ADFStack stack,
            final GPIndividual individual,
            final Problem problem) {
    	IntData rd = ((IntData)(input));
    	rd.x = ((CLIAProblem)problem).currentInputs[16];
    }
}
