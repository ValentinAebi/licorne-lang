package licorne.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

class FilePrimitives {
    public static final FilePrimitives INSTANCE = new FilePrimitives();

    String[] readAllLines(String path) throws IOException {
        return Files.readAllLines(Path.of(path))
                    .stream()
                    .toArray((sz) -> new String[sz]);
    }

    int writeFile(String path, String content) throws IOException {
        Files.writeString(Path.of(path), content);
        return 0;
    }

}
