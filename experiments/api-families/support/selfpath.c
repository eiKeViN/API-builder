#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* This executor exposes /proc/self/exe but its procfs PID namespace differs
 * from getpid(). Normalize only the current executable's equivalent path. */
ssize_t readlink(const char *path, char *buf, size_t size) {
    char self[64];
    snprintf(self, sizeof(self), "/proc/%d/exe", (int)getpid());
    if (strcmp(path, self) == 0) path = "/proc/self/exe";
    ssize_t (*next)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    return next(path, buf, size);
}
