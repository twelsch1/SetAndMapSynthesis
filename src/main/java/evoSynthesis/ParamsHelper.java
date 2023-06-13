package evoSynthesis;

import java.util.ArrayList;
import java.util.Map;

import static java.util.Map.entry;

import ec.util.Parameter;
import ec.util.ParameterDatabase;

public class ParamsHelper {

	
	public static void setFunctionSet(ParameterDatabase dbase, String[] variables, String[] definedFunctions) {
	
		
		Map<String, String> definedFunctionsMap = Map.ofEntries(
			    entry("one-times", "OneTimes"),
			    entry("two-times", "TwoTimes"),
			    entry("three-times", "ThreeTimes"),
			    entry("four-times", "FourTimes"),
			    entry("five-times", "FiveTimes"),
			    entry("six-times", "SixTimes"),
			    entry("seven-times", "SevenTimes"),
			    entry("eight-times", "EightTimes"),
			    entry("nine-times", "NineTimes"),
			    entry("ten-times", "TenTimes"),
			    entry("eleven-times", "ElevenTimes"),
			    entry("minus", "Minus"),
			    entry("plus2", "PlusTwo"),
			    entry("plus3", "PlusThree"),
			    entry("plus4", "PlusFour"),
			    entry("plus5", "PlusFive"),
			    entry("plus6", "PlusSix"),
			    entry("plus7", "PlusSeven"),
			    entry("plus8", "PlusEight"),
			    entry("plus9", "PlusNine"),
			    entry("or3", "OrThree"),
			    entry("iteB", "IM")
			);
		
		Map<String, String> definedFunctionsTypeMap = Map.ofEntries(
		    entry("one-times", "nc1"),
		    entry("two-times", "nc1"),
		    entry("three-times", "nc1"),
		    entry("four-times", "nc1"),
		    entry("five-times", "nc1"),
		    entry("six-times", "nc1"),
		    entry("seven-times", "nc1"),
		    entry("eight-times", "nc1"),
		    entry("nine-times", "nc1"),
		    entry("ten-times", "nc1"),
		    entry("eleven-times", "nc1"),
		    entry("minus", "nc1"),
		    entry("plus2", "nc2"),
		    entry("plus3", "nc3"),
		    entry("plus4", "nc4"),
		    entry("plus5", "nc5"),
		    entry("plus6", "nc6"),
		    entry("plus7", "nc7"),
		    entry("plus8", "nc8"),
		    entry("plus9", "nc9"),
		    entry("or3", "ncboolthree"),
		    entry("iteB", "ncboolthree")
		);
		
		ArrayList<String> functions = new ArrayList<>();
		ArrayList<String> functionTypes = new ArrayList<>();
		
		//add standard LIA operators
		
		functions.add("functions.integer.Add");
		functionTypes.add("nc2");
		
		functions.add("functions.integer.Sub");
		functionTypes.add("nc2");
		
		
		functions.add("functions.integer.Mul");
		functionTypes.add("ncmult");
		
		
		functions.add("functions.integer.GT");
		functionTypes.add("nccomp");
		
		functions.add("functions.integer.LT");
		functionTypes.add("nccomp");
		
		functions.add("functions.integer.GTE");
		functionTypes.add("nccomp");
		
		functions.add("functions.integer.LTE");
		functionTypes.add("nccomp");
		
		functions.add("functions.integer.Equals");
		functionTypes.add("nccomp");
		
		functions.add("functions.integer.And");
		functionTypes.add("ncandor");
		
		functions.add("functions.integer.Or");
		functionTypes.add("ncandor");
		
		functions.add("functions.integer.Not");
		functionTypes.add("ncnot");
		
		functions.add("functions.integer.ITE");
		functionTypes.add("ncite");
		
		functions.add("functions.integer.Ephemeral");
		functionTypes.add("ncephem");
		
		functions.add("functions.integer.Ephemeral");
		functionTypes.add("nc0");
		
		functions.add("functions.integer.EphemeralBoolean");
		functionTypes.add("nc0bool");
		
		// Add definedFunctions
		
		/*if (definedFunctions != null) {
			for (int i = 0; i < definedFunctions.length; i++) {
				String definedFunction = definedFunctions[i];
				functions.add("functions.defined." + definedFunctionsMap.get(definedFunction));
				functionTypes.add(definedFunctionsTypeMap.get(definedFunction));
			}
		}*/
		
		//Add variables
		for (int i = 1; i <= variables.length; i++ ) {
			functions.add("variables.Var"+i);
			functionTypes.add("nc0");
		}
		
		//Add function set to the database
		dbase.set(new Parameter("gp.fs.0.size"), Integer.toString(functions.size()));
		for (int i = 0; i < functions.size(); i++) {
			//System.out.println(functions.get(i));
			dbase.set(new Parameter("gp.fs.0.func."+i), functions.get(i));
			dbase.set(new Parameter("gp.fs.0.func."+i+".nc"), functionTypes.get(i));
		}
		
	}
}

