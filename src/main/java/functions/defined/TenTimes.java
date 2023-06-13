package functions.defined;

import datatypes.IntData;
import ec.EvolutionState;
import ec.Problem;
import ec.gp.ADFStack;
import ec.gp.GPData;
import ec.gp.GPIndividual;
import ec.gp.GPNode;

@SuppressWarnings("serial")
public class TenTimes extends GPNode {
	
	public String toString() { return "ten-times"; }

	public int expectedChildren() { return 1; }

	public void eval(final EvolutionState state,
                 final int thread,
                 final GPData input,
                 final ADFStack stack,
                 final GPIndividual individual,
                 final Problem problem) {
	    IntData rd = ((IntData)(input));
	
	    children[0].eval(state,thread,input,stack,individual,problem);
	    rd.x *= 10;
    }
}
