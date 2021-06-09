import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class ColoniaTest {
	Colonia colony;
	private int inputIncrease;
	private int expectedResult;
	
	
	@Parameters
	public static Collection<Object[]> creaParametri() {
		return Arrays.asList(new Object[][] {
			{50,150},
			{100,200},
			{-100,100},
		});
	}
	
	public ColoniaTest(int p1, int p2) {
		colony = new Colonia("aa01", 2020, 4, 100, new ArrayList<Report>());
		inputIncrease = p1;
		expectedResult = p2;
	}
	
	@Test
	public void testIncreaseHoney() {
		colony.increaseTotalHoney(inputIncrease);
		
		assertEquals(expectedResult,colony.getTotalHoney());
	}
	
}
