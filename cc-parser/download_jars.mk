CUP_JAR = $(PARSER_LIBDIR)/java-cup-11b.jar
JFLEX_PLUGIN_JAR = $(PARSER_LIBDIR)/jflex-1.9.1.jar

.PHONY: download-jars
download-jars: $(CUP_JAR) $(CUP_RUNTIME_JAR) $(JFLEX_PLUGIN_JAR)

$(PARSER_LIBDIR):
	@mkdir -p $@

$(CUP_JAR): | $(PARSER_LIBDIR)
	@echo "Looking for CUP JAR at $(CUP_JAR)..."
	@if [ ! -f $(CUP_JAR) ]; then \
			echo "CUP JAR not found, downloading..."; \
	    mvn org.apache.maven.plugins:maven-dependency-plugin:2.10:get \
	        -DremoteRepositories=https://repo.maven.apache.org/maven2/ \
	        -Dartifact=com.github.vbmacher:java-cup:11b-20160615-2 \
	        -Dtransitive=false \
	        -Ddest=$(CUP_JAR); \
	else \
			echo "CUP JAR found, skipping download."; \
	fi

$(JFLEX_PLUGIN_JAR): | $(PARSER_LIBDIR)
	@echo "Looking for JFlex plugin JAR at $(JFLEX_PLUGIN_JAR)..."
	@if [ ! -f $(JFLEX_PLUGIN_JAR) ]; then \
	    echo "JFlex plugin JAR not found, downloading..."; \
	    mvn org.apache.maven.plugins:maven-dependency-plugin:2.10:get \
	        -DremoteRepositories=https://repo.maven.apache.org/maven2/ \
	        -Dartifact=de.jflex:jflex:1.9.1 \
	        -Dtransitive=false \
	        -Ddest=$(JFLEX_PLUGIN_JAR); \
	else \
			echo "JFlex plugin JAR found, skipping download."; \
	fi
