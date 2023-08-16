package functions.integer;

//import java.util.Random;

import datatypes.IntData;
import ec.EvolutionState;
import ec.Problem;
import ec.gp.ADFStack;
import ec.gp.ERC;
import ec.gp.GPData;
import ec.gp.GPIndividual;
import ec.gp.GPNode;
import ec.util.Code;
import ec.util.DecodeReturn;

@SuppressWarnings("serial")
public class EphemeralBoolean extends ERC {

	int value;
	
	public String toStringForHumans() { return value == 1 ? "true" : "false"; }
	
    @Override
    public void eval(final EvolutionState state,
            final int thread,
            final GPData input,
            final ADFStack stack,
            final GPIndividual individual,
            final Problem problem) {
    	((IntData)(input)).x = value;
    }

	@Override
	public void resetNode(EvolutionState state, int thread) {
		// TODO Auto-generated method stub
		value = state.random[thread].nextInt(2); 
	}

	@Override
	public boolean nodeEquals(GPNode node) {
		return (node.getClass() == this.getClass() && ((EphemeralBoolean)node).value == value); 
	}

	@Override
	public String encode() {
		return Code.encode(value==1);
	}
	
	public boolean decode(DecodeReturn dret) {
		int pos = dret.pos;
		String data = dret.data;
		Code.decode(dret);
		if (dret.type != DecodeReturn.T_BOOLEAN) // uh oh! Restore and signal error.
		{ dret.data = data; dret.pos = pos; return false; }
		value = (int) dret.l;
		return true;
		}

}

