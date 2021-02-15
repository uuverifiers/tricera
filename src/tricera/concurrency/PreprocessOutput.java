package tricera.concurrency;

import com.sun.jna.*;

import java.util.Arrays;
import java.util.List;

public class PreprocessOutput extends Structure implements Structure.ByValue {
    public int numRecursiveFuns;
    public boolean usesArrays;
    public boolean isUnsupported;
    public boolean hasErrorOccurred;
    public String outputBuffer;

    @Override
    protected List<String> getFieldOrder() {
        return Arrays.asList(new String[]{
                "numRecursiveFuns", "usesArrays", "isUnsupported",
                "hasErrorOccurred", "outputBuffer"});
    }
};