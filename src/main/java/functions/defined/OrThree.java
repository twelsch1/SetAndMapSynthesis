package functions.defined;

import datatypes.IntData;
import ec.EvolutionState;
import ec.Problem;
import ec.gp.ADFStack;
import ec.gp.GPData;
import ec.gp.GPIndividual;
import ec.gp.GPNode;

@SuppressWarnings("serial")
public class OrThree extends GPNode {

	public String toString() {
		return "or3";
	}

	public int expectedChildren() {
		return 3;
	}

	public void eval(final EvolutionState state, final int thread, final GPData input, final ADFStack stack,
			final GPIndividual individual, final Problem problem) {

		
		IntData id = ((IntData) (input));
		int result = 0;
		for (int i = 0; i < children.length; i++) {
			children[i].eval(state, thread, input, stack, individual, problem);
			if (id.x == 1) {
				result = 1;
			}
		}
		
		
		id.x = result;
	}

}
