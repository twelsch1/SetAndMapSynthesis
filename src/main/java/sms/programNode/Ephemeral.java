package sms.programNode;


import sms.datatypes.IntData;

public class Ephemeral extends Node {

	int value;
	IntData rd = new IntData();

	public String toString() {
		return "" + value;
	}
	
	public String getNodeType() { return "int";}

	@Override
	public void eval(final IntData input, final int[] variables) {
		input.x = value;
	}

	public Ephemeral(int value) {
		this.value = value;
	}

}
