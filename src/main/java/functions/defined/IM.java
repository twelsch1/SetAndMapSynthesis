package functions.defined;

import datatypes.IntData;
import ec.EvolutionState;
import ec.Problem;
import ec.gp.ADFStack;
import ec.gp.GPData;
import ec.gp.GPIndividual;
import ec.gp.GPNode;

@SuppressWarnings("serial")
public class IM extends GPNode {

	public String toString() {
		return "iteB";
	}

	public int expectedChildren() {
		return 3;
	}

	public void eval(final EvolutionState state, final int thread, final GPData input, final ADFStack stack,
			final GPIndividual individual, final Problem problem) {

		
		IntData id = ((IntData) (input));

		children[0].eval(state, thread, input, stack, individual, problem);
		
		if (id.x == 1) {
			children[1].eval(state, thread, input, stack, individual, problem);
		} else {
			children[2].eval(state, thread, input, stack, individual, problem);
		}
	}

}
