package datatypes;
import ec.gp.GPData;

@SuppressWarnings("serial")
public class IntData extends GPData {
	public int x;
	
	public void copyTo(final GPData gpd) {
		((IntData)gpd).x = x; 
	}	
}
