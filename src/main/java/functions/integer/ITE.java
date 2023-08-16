package functions.integer;

import datatypes.IntData;
import ec.EvolutionState;
import ec.Problem;
import ec.gp.ADFStack;
import ec.gp.GPData;
import ec.gp.GPIndividual;
import ec.gp.GPNode;

@SuppressWarnings("serial")
public class ITE extends GPNode {

	public String toString() {
		return "ite";
	}

	public int expectedChildren() {
		return 3;
	}
	
	private int ignoreOptions = 0;
	

	public void eval(final EvolutionState state, final int thread, final GPData input, final ADFStack stack,
			final GPIndividual individual, final Problem problem) {

		
		IntData id = ((IntData) (input));
		
		if (ignoreOptions == 0) {

			children[0].eval(state, thread, input, stack, individual, problem);

			if (id.x == 1) {
				children[1].eval(state, thread, input, stack, individual, problem);
			} else {
				children[2].eval(state, thread, input, stack, individual, problem);
			}
		} else if (ignoreOptions == 1) {
			children[1].eval(state, thread, input, stack, individual, problem);
		} else {
			children[2].eval(state, thread, input, stack, individual, problem);
		}
	}

	public void setIgnoreOptions(int ignoreOptions) {
		this.ignoreOptions = ignoreOptions;
	}
	
	

}
