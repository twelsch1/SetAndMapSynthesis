package bcs.main;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class AdditionalTerm implements Comparable<AdditionalTerm> {

	private String term;
	
	public AdditionalTerm(String term) {
		this.term = term;
	}

	@Override
	public int compareTo(AdditionalTerm comp) {
		return Integer.compare(comp.getTerm().length(), this.getTerm().length());
	}

	public String getTerm() {
		return term;
	}

	public void setTerm(String term) {
		this.term = term;
	}

	
	
	
	
	
}
