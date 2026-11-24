#include <iostream>
#include <iomanip>
#include <string>
#include <sstream>
#include <limits>
#include <cctype>
#include <ctime>
#include <cstdio>
#include <conio.h>

using namespace std;

int readPIN() {
    int pin = 0;
    char ch;
    cout << "Enter PIN: ";

    while ((ch = getch()) != '\r') {
        if (ch == '\b') {
            if (pin > 0) {
                pin /= 10;
                cout << "\b \b";
            }
        } else if (ch >= '0' && ch <= '9') {
            pin = pin * 10 + (ch - '0');
            cout << '*';
        }
    }

    cout << '\n';
    return pin;
}

const int MAX_STUDENTS = 300;
const int MAX_ROOMS = 35;
const int MAX_LOGS = 1000;
const int MAX_VISITORS = 200;
const int MAX_LEAVES = 200;
const int MAX_NOTICES = 100;
const int MAX_BOOKINGS = 500;

struct Student {
    int id;
    string name, department, contact, guardian, emergency;
    double gpa;
    int merit;
    bool returningStudent, active, outside, suspended;
    int roomIndex, bed, bookingId;
    double deposit, balance;
    int lateCount, violationLevel;
};

struct Room {
    int floor, number, type, capacity, occupied;
    int occupants[4];
};

struct Booking {
    int id, studentId, roomIndex, bed;
    time_t depositDeadline;
    bool active, confirmed;
};

struct GateLog {
    int studentId, type, late, emergency;
    time_t timestamp;
};

struct Visitor {
    int studentId;
    string name, identity;
    time_t inTime, outTime;
    bool active;
};

struct LeaveRequest {
    int id, studentId;
    time_t fromTime, toTime;
    string reason;
    int status;
};

struct Notice {
    string message;
};


// Internal graph of room-to-student relationships. This supports existing
// room occupancy checks and the room map; it does not add a separate feature.
class RoomStudentGraph {
private:
    static const int MAX_NODES = MAX_ROOMS + MAX_STUDENTS;
    int head[MAX_NODES];
    int to[MAX_STUDENTS * 2];
    int next[MAX_STUDENTS * 2];
    int edgeCount;
public:
    RoomStudentGraph() : edgeCount(0) {
        for (int i = 0; i < MAX_NODES; i++) head[i] = -1;
    }
    void addConnection(int roomNode, int studentNode) {
        to[edgeCount] = studentNode;
        next[edgeCount] = head[roomNode];
        head[roomNode] = edgeCount++;
        to[edgeCount] = roomNode;
        next[edgeCount] = head[studentNode];
        head[studentNode] = edgeCount++;
    }
    int countStudentsConnectedToRoom(int roomNode) const {
        bool visited[MAX_NODES] = {false};
        int queue[MAX_NODES];
        int front = 0, rear = 0, count = 0;
        visited[roomNode] = true;
        queue[rear++] = roomNode;
        while (front < rear) {
            int current = queue[front++];
            for (int edge = head[current]; edge != -1; edge = next[edge]) {
                int neighbor = to[edge];
                if (!visited[neighbor]) {
                    visited[neighbor] = true;
                    queue[rear++] = neighbor;
                    if (neighbor >= MAX_ROOMS) count++;
                }
            }
        }
        return count;
    }
};

struct Complaint {
    int id, studentId, category, priority, status;
    string description, remark;
};

struct WaitNode {
    int studentId;
    WaitNode *next;
};

struct ComplaintNode {
    Complaint data;
    ComplaintNode *next;
};


// Dynamic array used by real student search/sort operations.
// Rule of Three: destructor, copy constructor and copy assignment own the buffer safely.
class DynamicIntArray {
    int *data;
    int length;
public:
    explicit DynamicIntArray(int n = 0) : data(n > 0 ? new int[n] : NULL), length(n) {}
    DynamicIntArray(const DynamicIntArray &other)
        : data(other.length > 0 ? new int[other.length] : NULL), length(other.length) {
        for (int i = 0; i < length; i++) data[i] = other.data[i];
    }
    DynamicIntArray &operator=(const DynamicIntArray &other) {
        if (this != &other) {
            int *copy = other.length > 0 ? new int[other.length] : NULL;
            for (int i = 0; i < other.length; i++) copy[i] = other.data[i];
            delete[] data;
            data = copy;
            length = other.length;
        }
        return *this;
    }
    ~DynamicIntArray() { delete[] data; }
    int &operator[](int index) { return data[index]; }
    const int &operator[](int index) const { return data[index]; }
    int size() const { return length; }
};

class HostelSystem {
private:
    Student students[MAX_STUDENTS];
    Room rooms[MAX_ROOMS];
    Booking bookings[MAX_BOOKINGS];
    GateLog gateLogs[MAX_LOGS];
    Visitor visitors[MAX_VISITORS];
    LeaveRequest leaves[MAX_LEAVES];
    Notice notices[MAX_NOTICES];

    int studentCount, roomCount, bookingCount, gateCount;
    int visitorCount, leaveCount, noticeCount;
    int nextBookingId, nextComplaintId, nextLeaveId;
    int wardenPin, guardPin;
    WaitNode *waitHead, *waitTail;
    ComplaintNode *complaintHead;
    int complaintCount;

    string complaintCategory(int c) {
        if (c == 1) return "Plumbing";
        if (c == 2) return "Electricity";
        if (c == 3) return "Internet";
        if (c == 4) return "Cleaning";
        return "Other";
    }

    string complaintStatus(int s) {
        if (s == 0) return "Open";
        if (s == 1) return "In Progress";
        return "Resolved";
    }

    string roomType(int t) {
        if (t == 1) return "Solo";
        if (t == 2) return "Double";
        if (t == 3) return "Interlinked Suite";
        return "Four-Bed Bunk";
    }

    string dateTimeText(time_t value) {
        if (value == 0) return "Not recorded";
        tm *local = localtime(&value);
        if (local == NULL) return "Unknown";
        char buffer[40];
        if (strftime(buffer, sizeof(buffer), "%Y-%m-%d %I:%M %p", local) == 0)
            return "Unknown";
        return string(buffer);
    }

    time_t currentTimestamp() {
        return time(NULL);
    }

    bool parseDateTime(const string &input, time_t &result) {
        int year, month, day, hour, minute;
        char extra;
        if (sscanf(input.c_str(), "%d-%d-%d %d:%d%c",
                   &year, &month, &day, &hour, &minute, &extra) != 5)
            return false;
        if (year < 2000 || month < 1 || month > 12 || day < 1 || day > 31 ||
            hour < 0 || hour > 23 || minute < 0 || minute > 59)
            return false;
        tm requested = {};
        requested.tm_year = year - 1900;
        requested.tm_mon = month - 1;
        requested.tm_mday = day;
        requested.tm_hour = hour;
        requested.tm_min = minute;
        requested.tm_isdst = -1;
        result = mktime(&requested);
        if (result == (time_t)-1) return false;
        tm *check = localtime(&result);
        return check != NULL && check->tm_year == year - 1900 &&
               check->tm_mon == month - 1 && check->tm_mday == day &&
               check->tm_hour == hour && check->tm_min == minute;
    }

    // Linear search through the student array.
    int findStudentIndex(int id) {
        for (int i = 0; i < studentCount; i++)
            if (students[i].id == id && students[i].active) return i;
        return -1;
    }

    int findStudentAny(int id) {
        for (int i = 0; i < studentCount; i++)
            if (students[i].id == id) return i;
        return -1;
    }

    int findRoom(int floor, int number) {
        for (int i = 0; i < roomCount; i++)
            if (rooms[i].floor == floor && rooms[i].number == number) return i;
        return -1;
    }

    int findBooking(int id) {
        for (int i = 0; i < bookingCount; i++)
            if (bookings[i].id == id && bookings[i].active) return i;
        return -1;
    }

    // Queue: linked-list waitlist maintains first-come, first-served order.
    void addWaitlist(int studentId) {
        WaitNode *node = new WaitNode;
        node->studentId = studentId;
        node->next = NULL;
        if (waitTail == NULL) waitHead = waitTail = node;
        else {
            waitTail->next = node;
            waitTail = node;
        }
        cout << "Student added to the room waitlist.\n";
    }

    void removeWaitlistStudent(int studentId) {
        WaitNode *cur = waitHead, *prev = NULL;
        while (cur != NULL) {
            if (cur->studentId == studentId) {
                if (prev == NULL) waitHead = cur->next;
                else prev->next = cur->next;
                if (cur == waitTail) waitTail = prev;
                delete cur;
                return;
            }
            prev = cur;
            cur = cur->next;
        }
    }

    bool isOnWaitlist(int studentId) {
        WaitNode *cur = waitHead;
        while (cur != NULL) {
            if (cur->studentId == studentId) return true;
            cur = cur->next;
        }
        return false;
    }

    // Priority queue concept: linked list is maintained in priority order.
    void addComplaintNode(const Complaint &c) {
        ComplaintNode *node = new ComplaintNode;
        node->data = c;
        node->next = NULL;
        if (complaintHead == NULL || c.priority < complaintHead->data.priority) {
            node->next = complaintHead;
            complaintHead = node;
        } else {
            ComplaintNode *cur = complaintHead;
            while (cur->next != NULL && cur->next->data.priority <= c.priority)
                cur = cur->next;
            node->next = cur->next;
            cur->next = node;
        }
        complaintCount++;
    }

    void updateComplaintNode(int id, int status, const string &remark) {
        ComplaintNode *cur = complaintHead;
        while (cur != NULL) {
            if (cur->data.id == id) {
                cur->data.status = status;
                cur->data.remark = remark;
                return;
            }
            cur = cur->next;
        }
    }

    // Room details and occupied beds are stored in fixed-size arrays.
    void initializeRooms() {
        roomCount = 0;
        for (int n = 1; n <= 8; n++) {
            Room r;
            r.floor = 1; r.number = n; r.type = 2; r.capacity = 2;
            r.occupied = 0;
            for (int j = 0; j < 4; j++) r.occupants[j] = -1;
            rooms[roomCount++] = r;
        }
        for (int n = 9; n <= 10; n++) {
            Room r;
            r.floor = 1; r.number = n; r.type = 3; r.capacity = 2;
            r.occupied = 0;
            for (int j = 0; j < 4; j++) r.occupants[j] = -1;
            rooms[roomCount++] = r;
        }
        for (int n = 1; n <= 4; n++) {
            Room r;
            r.floor = 2; r.number = n; r.type = 1; r.capacity = 1;
            r.occupied = 0;
            for (int j = 0; j < 4; j++) r.occupants[j] = -1;
            rooms[roomCount++] = r;
        }
        for (int n = 5; n <= 12; n++) {
            Room r;
            r.floor = 2; r.number = n; r.type = 2; r.capacity = 2;
            r.occupied = 0;
            for (int j = 0; j < 4; j++) r.occupants[j] = -1;
            rooms[roomCount++] = r;
        }
        for (int n = 1; n <= 8; n++) {
            Room r;
            r.floor = 3; r.number = n; r.type = 2; r.capacity = 2;
            r.occupied = 0;
            for (int j = 0; j < 4; j++) r.occupants[j] = -1;
            rooms[roomCount++] = r;
        }
        for (int n = 9; n <= 11; n++) {
            Room r;
            r.floor = 3; r.number = n; r.type = 4; r.capacity = 4;
            r.occupied = 0;
            for (int j = 0; j < 4; j++) r.occupants[j] = -1;
            rooms[roomCount++] = r;
        }
    }

    // Three fictional sample student records are loaded at startup for demonstration.
    void initializeSampleStudents() {
        Student sample;

        sample.id = 1001;
        sample.name = "Ahmed Khan";
        sample.department = "Software Engineering";
        sample.contact = "0300-1112233";
        sample.guardian = "0301-2223344";
        sample.emergency = "0302-3334455";
        sample.gpa = 0.0;
        sample.merit = 24;
        sample.returningStudent = false;
        sample.active = true;
        sample.outside = false;
        sample.suspended = false;
        sample.roomIndex = -1;
        sample.bed = -1;
        sample.bookingId = -1;
        sample.deposit = 0;
        sample.balance = 0;
        sample.lateCount = 0;
        sample.violationLevel = 0;
        students[studentCount++] = sample;

        sample.id = 1002;
        sample.name = "Ayesha Malik";
        sample.department = "Computer Science";
        sample.contact = "0303-4445566";
        sample.guardian = "0304-5556677";
        sample.emergency = "0305-6667788";
        sample.gpa = 0.0;
        sample.merit = 86;
        sample.returningStudent = false;
        sample.active = true;
        sample.outside = false;
        sample.suspended = false;
        sample.roomIndex = -1;
        sample.bed = -1;
        sample.bookingId = -1;
        sample.deposit = 0;
        sample.balance = 0;
        sample.lateCount = 0;
        sample.violationLevel = 0;
        students[studentCount++] = sample;

        sample.id = 1003;
        sample.name = "Bilal Ahmed";
        sample.department = "Electrical Engineering";
        sample.contact = "0306-7778899";
        sample.guardian = "0307-8889900";
        sample.emergency = "0308-9990011";
        sample.gpa = 3.62;
        sample.merit = 0;
        sample.returningStudent = true;
        sample.active = true;
        sample.outside = false;
        sample.suspended = false;
        sample.roomIndex = -1;
        sample.bed = -1;
        sample.bookingId = -1;
        sample.deposit = 0;
        sample.balance = 0;
        sample.lateCount = 0;
        sample.violationLevel = 0;
        students[studentCount++] = sample;
    }

    int entitledFloor(const Student &s) {
        if (s.returningStudent) {
            if (s.gpa >= 3.5) return 1;
            if (s.gpa >= 2.5) return 2;
            return 3;
        }
        if (s.merit <= 50) return 1;
        if (s.merit <= 150) return 2;
        return 3;
    }

    int graphRoomOccupancy(int roomIndex) {
        RoomStudentGraph graph;
        for (int i = 0; i < studentCount; i++) {
            if (students[i].active && students[i].roomIndex >= 0 &&
                students[i].roomIndex < roomCount)
                graph.addConnection(students[i].roomIndex, MAX_ROOMS + i);
        }
        return graph.countStudentsConnectedToRoom(roomIndex);
    }

    bool roomAllowed(const Student &s, const Room &r) {
        int roomIndex = (int)(&r - rooms);
        if (graphRoomOccupancy(roomIndex) >= r.capacity) return false;
        int floorLimit = entitledFloor(s);
        if (r.floor < floorLimit) return false;
        if (r.type == 1 && !(s.returningStudent && s.gpa >= 4.0 && r.floor == 2))
            return false;
        return true;
    }

    int rentForRoom(int type) {
        if (type == 1) return 18000;
        if (type == 2) return 12000;
        if (type == 3) return 15000;
        return 9000;
    }

    int depositForRoom(int type) {
        return rentForRoom(type);
    }

    int calculateFine(int lateCount) {
        if (lateCount <= 0) return 0;
        return 500 * lateCount * lateCount;
    }

    void showStudent(const Student &s) {
        cout << "\nStudent ID: " << s.id << "\nName: " << s.name
             << "\nDepartment: " << s.department << "\nContact: " << s.contact
             << "\nGuardian: " << s.guardian << "\nEmergency Contact: " << s.emergency
             << "\nAdmission Type: " << (s.returningStudent ? "Returning" : "New")
             << "\nGPA: " << fixed << setprecision(2) << s.gpa
             << "\nMerit Number: " << s.merit
             << "\nStatus: " << (s.active ? "Active" : "Checked Out");
        if (s.roomIndex >= 0 && s.roomIndex < roomCount)
            cout << "\nRoom: Floor " << rooms[s.roomIndex].floor
                 << ", Room " << rooms[s.roomIndex].number
                 << ", Bed " << s.bed;
        else cout << "\nRoom: Not allocated";
        cout << "\nBalance: Rs. " << s.balance << "\n";
    }

    void printRoom(const Room &r) {
        int roomIndex = (int)(&r - rooms);
        int occupied = graphRoomOccupancy(roomIndex);
        string state = occupied == 0 ? "VACANT" :
                       (occupied == r.capacity ? "FULL" : "PARTLY FILLED");
        cout << left << setw(8) << r.floor << setw(9) << r.number
             << setw(22) << roomType(r.type) << setw(10)
             << occupied << "/" << r.capacity << state << "\n";
    }
    void displayRoomMap() {
        cout << "\nROOM MAP: VACANT = GREEN, PARTLY FILLED = YELLOW, FULL = RED\n";
        for (int floor = 1; floor <= 3; floor++) {
            cout << "\nFLOOR " << floor << "\n";
            cout << left << setw(8) << "Floor" << setw(9) << "Room"
                 << setw(22) << "Type" << setw(10) << "Beds" << "Status\n";
            for (int i = 0; i < roomCount; i++)
                if (rooms[i].floor == floor) printRoom(rooms[i]);
        }
    }

    void addStudent() {
        if (studentCount >= MAX_STUDENTS) {
            cout << "Student capacity reached.\n";
            return;
        }
        Student s;
        cout << "Enter student ID: ";
        cin >> s.id;
        if (findStudentAny(s.id) != -1) {
            cout << "This ID already exists.\n";
            return;
        }
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        cout << "Full name: "; getline(cin, s.name);
        cout << "Department: "; getline(cin, s.department);
        cout << "Contact number: "; getline(cin, s.contact);
        cout << "Guardian contact: "; getline(cin, s.guardian);
        cout << "Emergency contact: "; getline(cin, s.emergency);
        int type;
        cout << "Admission type (1 returning, 2 new): ";
        cin >> type;
        s.returningStudent = (type == 1);
        cout << "GPA (enter 0 if new student): ";
        cin >> s.gpa;
        cout << "Merit number (enter 0 if returning student): ";
        cin >> s.merit;
        s.active = true; s.outside = false; s.suspended = false;
        s.roomIndex = -1; s.bed = -1; s.bookingId = -1;
        s.deposit = 0; s.balance = 0; s.lateCount = 0;
        s.violationLevel = 0;
        students[studentCount++] = s;
        cout << "Student profile created successfully.\n";
    }

    // AVL tree index is rebuilt from active records to avoid stale entries.
    struct StudentTreeNode {
        int id, studentIndex, height;
        StudentTreeNode *left, *right;
        StudentTreeNode(int value, int index) : id(value), studentIndex(index), height(1), left(NULL), right(NULL) {}
    };

    StudentTreeNode *avlRotateRight(StudentTreeNode *y) {
        StudentTreeNode *x = y->left, *t = x->right;
        x->right = y; y->left = t;
        y->height = 1 + ((y->left ? y->left->height : 0) > (y->right ? y->right->height : 0) ? (y->left ? y->left->height : 0) : (y->right ? y->right->height : 0));
        x->height = 1 + ((x->left ? x->left->height : 0) > (x->right ? x->right->height : 0) ? (x->left ? x->left->height : 0) : (x->right ? x->right->height : 0));
        return x;
    }

    StudentTreeNode *avlRotateLeft(StudentTreeNode *x) {
        StudentTreeNode *y = x->right, *t = y->left;
        y->left = x; x->right = t;
        x->height = 1 + ((x->left ? x->left->height : 0) > (x->right ? x->right->height : 0) ? (x->left ? x->left->height : 0) : (x->right ? x->right->height : 0));
        y->height = 1 + ((y->left ? y->left->height : 0) > (y->right ? y->right->height : 0) ? (y->left ? y->left->height : 0) : (y->right ? y->right->height : 0));
        return y;
    }

    StudentTreeNode *avlInsert(StudentTreeNode *root, int id, int index) {
        if (!root) return new StudentTreeNode(id, index);
        if (id < root->id) root->left = avlInsert(root->left, id, index);
        else if (id > root->id) root->right = avlInsert(root->right, id, index);
        else return root;
        int lh = root->left ? root->left->height : 0;
        int rh = root->right ? root->right->height : 0;
        root->height = 1 + (lh > rh ? lh : rh);
        int balance = lh - rh;
        if (balance > 1 && id < root->left->id) return avlRotateRight(root);
        if (balance < -1 && id > root->right->id) return avlRotateLeft(root);
        if (balance > 1 && id > root->left->id) { root->left = avlRotateLeft(root->left); return avlRotateRight(root); }
        if (balance < -1 && id < root->right->id) { root->right = avlRotateRight(root->right); return avlRotateLeft(root); }
        return root;
    }

    StudentTreeNode *treeFind(StudentTreeNode *root, int id) {
        if (!root || root->id == id) return root;
        return id < root->id ? treeFind(root->left, id) : treeFind(root->right, id);
    }

    void freeStudentTree(StudentTreeNode *root) {
        if (!root) return;
        freeStudentTree(root->left); freeStudentTree(root->right); delete root;
    }

    int findStudentUsingAVL(int id) {
        StudentTreeNode *root = NULL;
        for (int i = 0; i < studentCount; i++) {
            if (students[i].active)
                root = avlInsert(root, students[i].id, i);
        }
        StudentTreeNode *match = treeFind(root, id);
        int result = match ? match->studentIndex : -1;
        freeStudentTree(root);
        return result;
    }

    // KMP is used internally for partial-name matching.
    bool nameContainsKMP(const string &name, const string &pattern) {
        if (pattern.empty()) return false;
        string text = name, key = pattern;
        for (size_t i = 0; i < text.length(); i++)
            text[i] = (char)tolower((unsigned char)text[i]);
        for (size_t i = 0; i < key.length(); i++)
            key[i] = (char)tolower((unsigned char)key[i]);

        int m = (int)key.length();
        int *lps = new int[m];
        lps[0] = 0;
        for (int i = 1, len = 0; i < m;) {
            if (key[i] == key[len]) lps[i++] = ++len;
            else if (len != 0) len = lps[len - 1];
            else lps[i++] = 0;
        }

        bool found = false;
        for (int i = 0, j = 0; i < (int)text.length();) {
            if (text[i] == key[j]) { i++; j++; }
            if (j == m) { found = true; break; }
            if (i < (int)text.length() && text[i] != key[j]) {
                if (j != 0) j = lps[j - 1];
                else i++;
            }
        }
        delete[] lps;
        return found;
    }

    void searchStudent() {
        int choice;
        cout << "Search by 1. Student ID  2. Student Name: ";
        cin >> choice;

        if (choice == 1) {
            int id;
            cout << "Enter student ID: ";
            cin >> id;
            int result = findStudentUsingAVL(id);
            if (result == -1) cout << "Student not found.\n";
            else showStudent(students[result]);
        } else if (choice == 2) {
            string name;
            cin.ignore(numeric_limits<streamsize>::max(), '\n');
            cout << "Enter full or partial student name: ";
            getline(cin, name);
            if (name.empty()) {
                cout << "Please enter a name to search.\n";
                return;
            }
            bool found = false;
            for (int i = 0; i < studentCount; i++) {
                if (students[i].active && nameContainsKMP(students[i].name, name)) {
                    showStudent(students[i]);
                    found = true;
                }
            }
            if (!found) cout << "No matching student found.\n";
        } else {
            cout << "Invalid search option.\n";
        }
    }

    // Merge sort is selected internally to display active student records alphabetically.
    void mergeStudentNames(DynamicIntArray &indexes, DynamicIntArray &temp, int left, int mid, int right) {
        int i = left, j = mid + 1, k = left;
        while (i <= mid && j <= right)
            temp[k++] = (students[indexes[i]].name <= students[indexes[j]].name) ? indexes[i++] : indexes[j++];
        while (i <= mid) temp[k++] = indexes[i++];
        while (j <= right) temp[k++] = indexes[j++];
        for (i = left; i <= right; i++) indexes[i] = temp[i];
    }

    void mergeSortStudentNames(DynamicIntArray &indexes, DynamicIntArray &temp, int left, int right) {
        if (left >= right) return;
        int mid = left + (right - left) / 2;
        mergeSortStudentNames(indexes, temp, left, mid);
        mergeSortStudentNames(indexes, temp, mid + 1, right);
        mergeStudentNames(indexes, temp, left, mid, right);
    }

    void listStudents() {
        int activeCount = 0;
        for (int i = 0; i < studentCount; i++)
            if (students[i].active) activeCount++;
        if (activeCount == 0) {
            cout << "No active student records found.\n";
            return;
        }

        DynamicIntArray indexes(activeCount), temp(activeCount);
        int count = 0;
        for (int i = 0; i < studentCount; i++)
            if (students[i].active) indexes[count++] = i;
        mergeSortStudentNames(indexes, temp, 0, activeCount - 1);

        cout << "\nID\tName\t\tAdmission\tRoom\tBalance\n";
        for (int i = 0; i < activeCount; i++) {
            const Student &student = students[indexes[i]];
            cout << student.id << "\t" << student.name << "\t"
                 << (student.returningStudent ? "Returning" : "New") << "\t";
            if (student.roomIndex >= 0)
                cout << rooms[student.roomIndex].floor << "-" << rooms[student.roomIndex].number;
            else cout << "None";
            cout << "\t" << student.balance << "\n";
        }
    }

    void allocateRoom(int loggedInStudent = -1) {
        int si = loggedInStudent;
        if (si < 0) {
            int id; cout << "Student ID: "; cin >> id;
            si = findStudentIndex(id);
        }
        if (si < 0 || si >= studentCount || !students[si].active) {
            cout << "Active student not found.\n";
            return;
        }
        int id = students[si].id;
        Student &s = students[si];
        if (s.roomIndex != -1) {
            cout << "Student already has a room.\n";
            return;
        }
        int floor = entitledFloor(s);
        cout << "Entitled floor: " << floor << " or a higher-numbered floor.\n";
        cout << "Eligible rooms are displayed below.\n";
        bool any = false;
        for (int i = 0; i < roomCount; i++) {
            if (roomAllowed(s, rooms[i])) {
                printRoom(rooms[i]); any = true;
            }
        }
        if (!any) {
            if (!isOnWaitlist(id)) addWaitlist(id);
            return;
        }
        int roomNo, chosenFloor;
        cout << "Enter floor and room number: ";
        cin >> chosenFloor >> roomNo;
        int ri = findRoom(chosenFloor, roomNo);
        if (ri == -1 || !roomAllowed(s, rooms[ri])) {
            cout << "Invalid or ineligible room selection.\n";
            return;
        }
        int bed = 1;
        while (bed <= rooms[ri].capacity) {
            bool used = false;
            for (int j = 0; j < rooms[ri].occupied; j++)
                if (rooms[ri].occupants[j] == bed) used = true;
            if (!used) break;
            bed++;
        }
        if (bookingCount >= MAX_BOOKINGS) {
            cout << "Booking storage full.\n";
            return;
        }
        rooms[ri].occupants[rooms[ri].occupied++] = bed;
        s.roomIndex = ri; s.bed = bed;
        s.bookingId = nextBookingId++;
        s.deposit = depositForRoom(rooms[ri].type);
        s.balance += s.deposit;
        Booking b;
        b.id = s.bookingId; b.studentId = id; b.roomIndex = ri; b.bed = bed;
        b.depositDeadline = currentTimestamp() + 3 * 24 * 60 * 60;
        b.active = true; b.confirmed = false;
        bookings[bookingCount++] = b;
        removeWaitlistStudent(id);
        cout << "\nBooking successful.\nBooking ID: " << b.id
             << "\nDeposit: Rs. " << s.deposit
             << "\nDeposit deadline: " << dateTimeText(b.depositDeadline)
             << "\nBooking will be cancelled if deposit is not cleared by deadline.\n";
    }

    // Array deletion: shift later bed entries left to fill the removed position.
    void clearRoomBed(int roomIndex, int bed) {
        if (roomIndex < 0 || roomIndex >= roomCount) return;
        Room &r = rooms[roomIndex];
        for (int i = 0; i < r.occupied; i++) {
            if (r.occupants[i] == bed) {
                for (int j = i; j < r.occupied - 1; j++)
                    r.occupants[j] = r.occupants[j + 1];
                r.occupants[r.occupied - 1] = -1;
                r.occupied--;
                return;
            }
        }
    }

    void processDeadlines() {
        for (int i = 0; i < bookingCount; i++) {
            if (bookings[i].active && !bookings[i].confirmed &&
                currentTimestamp() > bookings[i].depositDeadline) {
                int si = findStudentIndex(bookings[i].studentId);
                if (si != -1) {
                    clearRoomBed(bookings[i].roomIndex, bookings[i].bed);
                    students[si].roomIndex = -1;
                    students[si].bed = -1;
                    students[si].bookingId = -1;
                    students[si].balance -= students[si].deposit;
                    students[si].deposit = 0;
                    cout << "Booking " << bookings[i].id << " cancelled due to missed deposit deadline.\n";
                    if (!isOnWaitlist(students[si].id)) addWaitlist(students[si].id);
                }
                bookings[i].active = false;
            }
        }
    }

    void confirmDeposit() {
        int id; cout << "Booking ID: "; cin >> id;
        int bi = findBooking(id);
        if (bi == -1) {
            cout << "Active booking not found.\n";
            return;
        }
        bookings[bi].confirmed = true;
        cout << "Deposit confirmed for booking " << id << ".\n";
    }

    void processWaitlist() {
        if (waitHead == NULL) {
            cout << "Waitlist is empty.\n";
            return;
        }
        WaitNode *cur = waitHead;
        cout << "\nWAITLIST\n";
        while (cur != NULL) {
            int si = findStudentIndex(cur->studentId);
            cout << "Student ID: " << cur->studentId;
            if (si != -1) cout << "  Name: " << students[si].name;
            cout << "\n";
            cur = cur->next;
        }
        cout << "Waitlist follows first-come, first-served order.\n";
    }

    void showBill(int si) {
        Student &s = students[si];
        int rent = s.roomIndex >= 0 ? rentForRoom(rooms[s.roomIndex].type) : 0;
        int fine = calculateFine(s.lateCount);
        cout << "\n========== HOSTEL BILL ==========\n";
        cout << "Student: " << s.name << " (" << s.id << ")\n";
        cout << "Monthly rent: Rs. " << rent << "\n";
        cout << "Security deposit: Rs. " << s.deposit << "\n";
        cout << "Late penalty: Rs. " << fine << "\n";
        cout << "Total payable: Rs. " << rent + s.deposit + fine << "\n";
        cout << "Recorded balance: Rs. " << s.balance << "\n";
        cout << "=================================\n";
    }

    void generateReceipt() {
        int id; cout << "Student ID: "; cin >> id;
        int si = findStudentIndex(id);
        if (si == -1) cout << "Student not found.\n";
        else showBill(si);
    }

    void recordPayment() {
        int id, amount;
        cout << "Student ID: "; cin >> id;
        int si = findStudentIndex(id);
        if (si == -1) {
            cout << "Student not found.\n";
            return;
        }
        cout << "Payment amount: Rs. "; cin >> amount;
        if (amount <= 0) {
            cout << "Invalid amount.\n";
            return;
        }
        students[si].balance -= amount;
        if (students[si].balance < 0) students[si].balance = 0;
        cout << "Payment recorded. Remaining balance: Rs. "
             << students[si].balance << "\n";
    }

    void defaultersList() {
        bool found = false;
        cout << "\nFEE DEFAULTERS\n";
        for (int i = 0; i < studentCount; i++) {
            if (students[i].active && students[i].balance > 0) {
                cout << students[i].id << "  " << students[i].name
                     << "  Due: Rs. " << students[i].balance << "\n";
                found = true;
            }
        }
        if (!found) cout << "No fee defaulters.\n";
    }

    void fileComplaint(int si) {
        Complaint c;
        c.id = nextComplaintId++;
        c.studentId = students[si].id;
        cout << "Category: 1 Plumbing 2 Electricity 3 Internet 4 Cleaning 5 Other: ";
        cin >> c.category;
        if (c.category < 1 || c.category > 5) c.category = 5;
        cout << "Priority: 1 Urgent 2 Normal 3 Low: ";
        cin >> c.priority;
        if (c.priority < 1 || c.priority > 3) c.priority = 3;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        cout << "Complaint description: ";
        getline(cin, c.description);
        c.status = 0; c.remark = "";
        addComplaintNode(c);
        cout << "Complaint submitted. Complaint ID: " << c.id << "\n";
    }

    // Linked-list traversal to find this student's complaint records.
    void trackComplaint(int studentId) {
        ComplaintNode *cur = complaintHead;
        bool found = false;
        while (cur != NULL) {
            if (cur->data.studentId == studentId) {
                cout << "ID: " << cur->data.id << "  "
                     << complaintCategory(cur->data.category) << "  "
                     << complaintStatus(cur->data.status) << "  Priority: "
                     << cur->data.priority << "\nDescription: "
                     << cur->data.description << "\nRemark: "
                     << cur->data.remark << "\n\n";
                found = true;
            }
            cur = cur->next;
        }
        if (!found) cout << "No complaints found.\n";
    }

    void viewComplaints() {
        if (complaintHead == NULL) {
            cout << "No complaints have been filed.\n";
            return;
        }
        ComplaintNode *cur = complaintHead;
        while (cur != NULL) {
            cout << "\nComplaint ID: " << cur->data.id
                 << "\nStudent ID: " << cur->data.studentId
                 << "\nCategory: " << complaintCategory(cur->data.category)
                 << "\nPriority: " << cur->data.priority
                 << "\nStatus: " << complaintStatus(cur->data.status)
                 << "\nDescription: " << cur->data.description
                 << "\nRemark: " << cur->data.remark << "\n";
            cur = cur->next;
        }
    }

    void resolveComplaint() {
        int id, status;
        cout << "Complaint ID: "; cin >> id;
        cout << "New status: 0 Open 1 In Progress 2 Resolved: ";
        cin >> status;
        if (status < 0 || status > 2) {
            cout << "Invalid status.\n";
            return;
        }
        string remark;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        cout << "Warden remark: "; getline(cin, remark);
        ComplaintNode *cur = complaintHead;
        while (cur != NULL) {
            if (cur->data.id == id) {
                updateComplaintNode(id, status, remark);
                cout << "Complaint updated.\n";
                return;
            }
            cur = cur->next;
        }
        cout << "Complaint ID not found.\n";
    }

    bool hasValidPass(int studentId) {
        time_t now = currentTimestamp();
        for (int i = 0; i < leaveCount; i++) {
            if (leaves[i].studentId == studentId && leaves[i].status == 1 &&
                now >= leaves[i].fromTime && now <= leaves[i].toTime)
                return true;
        }
        return false;
    }

    void addGateLog(int studentId, int type, int emergency) {
        if (gateCount >= MAX_LOGS) {
            cout << "Gate log storage full.\n";
            return;
        }
        GateLog g;
        time_t now = currentTimestamp();
        tm *localNow = localtime(&now);
        int minutesNow = localNow ? localNow->tm_hour * 60 + localNow->tm_min : 0;
        g.studentId = studentId; g.timestamp = now; g.type = type;
        g.late = (type == 1 && minutesNow >= 1320 && !hasValidPass(studentId) && !emergency);
        g.emergency = emergency;
        gateLogs[gateCount++] = g;
        int si = findStudentIndex(studentId);
        if (si != -1) {
            if (type == 1) students[si].outside = false;
            else students[si].outside = true;
            if (g.late) {
                students[si].lateCount++;
                students[si].violationLevel++;
                int fine = calculateFine(students[si].lateCount);
                students[si].balance += fine;
                cout << "LATE ENTRY VIOLATION. Penalty level: "
                     << students[si].violationLevel << "  Fine: Rs. " << fine << "\n";
                if (students[si].violationLevel == 1) cout << "Level 1: Warning issued.\n";
                else if (students[si].violationLevel == 2) cout << "Level 2: Fine applied.\n";
                else if (students[si].violationLevel == 3) cout << "Level 3: Guardian contact required.\n";
                else {
                    students[si].suspended = true;
                    cout << "Level 4: Referred to disciplinary committee; student suspended pending review.\n";
                }
            } else if (type == 1) cout << "Normal entry recorded.\n";
            else cout << "Sign-out recorded.\n";
        }
    }

    void gateAction() {
        int id, action;
        cout << "Student ID: "; cin >> id;
        int si = findStudentIndex(id);
        if (si == -1) {
            cout << "Active student not found.\n";
            return;
        }
        cout << "1 Sign-out  2 Sign-in  3 Emergency entry: ";
        cin >> action;
        if (action == 1) addGateLog(id, 2, 0);
        else if (action == 2) addGateLog(id, 1, 0);
        else if (action == 3) addGateLog(id, 1, 1);
        else cout << "Invalid option.\n";
    }

    void outsideAtCurfew() {
        cout << "\nSTUDENTS OUTSIDE AT 10 PM\n";
        bool found = false;
        for (int i = 0; i < studentCount; i++) {
            if (students[i].active && students[i].outside) {
                cout << students[i].id << "  " << students[i].name << "\n";
                found = true;
            }
        }
        if (!found) cout << "No students are currently marked outside.\n";
    }

    void visitorEntry() {
        if (visitorCount >= MAX_VISITORS) {
            cout << "Visitor log full.\n";
            return;
        }
        Visitor v;
        cout << "Host student ID: "; cin >> v.studentId;
        if (findStudentIndex(v.studentId) == -1) {
            cout << "Host student not found.\n";
            return;
        }
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        cout << "Visitor full name: "; getline(cin, v.name);
        cout << "Visitor identity number: "; getline(cin, v.identity);
        v.inTime = currentTimestamp();
        tm *entryTime = localtime(&v.inTime);
        if (entryTime == NULL || entryTime->tm_hour < 8 || entryTime->tm_hour >= 20) {
            cout << "Visitor entry is allowed only between 08:00 AM and 08:00 PM.\n";
            return;
        }
        v.outTime = 0;
        v.active = true;
        visitors[visitorCount++] = v;
        cout << "Visitor entry recorded at " << dateTimeText(v.inTime)
             << ". Female visitor approval must be verified by guard.\n";
    }

    void visitorExit() {
        int index;
        cout << "Visitor record number (1-" << visitorCount << "): ";
        cin >> index;
        if (index < 1 || index > visitorCount) {
            cout << "Invalid record number.\n";
            return;
        }
        if (!visitors[index - 1].active) {
            cout << "This visitor has already exited.\n";
            return;
        }
        visitors[index - 1].outTime = currentTimestamp();
        visitors[index - 1].active = false;
        cout << "Visitor exit recorded at "
             << dateTimeText(visitors[index - 1].outTime) << ".\n";
    }

    void requestLeave(int si) {
        if (leaveCount >= MAX_LEAVES) {
            cout << "Leave request storage full.\n";
            return;
        }
        LeaveRequest l;
        l.id = nextLeaveId++;
        l.studentId = students[si].id;
        string fromText, toText;
        cout << "Leave start (YYYY-MM-DD HH:MM): ";
        getline(cin >> ws, fromText);
        cout << "Leave end   (YYYY-MM-DD HH:MM): ";
        getline(cin, toText);
        if (!parseDateTime(fromText, l.fromTime) ||
            !parseDateTime(toText, l.toTime) ||
            l.fromTime <= currentTimestamp() || l.toTime <= l.fromTime) {
            cout << "Invalid leave period. Enter a future start and a later end date/time.\n";
            return;
        }
        cout << "Reason: "; getline(cin, l.reason);
        l.status = 0;
        leaves[leaveCount++] = l;
        cout << "Leave request submitted. Request ID: " << l.id << "\n";
    }

    void manageLeaves() {
        bool any = false;
        for (int i = 0; i < leaveCount; i++) {
            cout << "\nRequest ID: " << leaves[i].id
                 << "  Student: " << leaves[i].studentId
                 << "  From: " << dateTimeText(leaves[i].fromTime)
                 << "  To: " << dateTimeText(leaves[i].toTime)
                 << "\nReason: " << leaves[i].reason
                 << "\nStatus: " << (leaves[i].status == 0 ? "Pending" :
                    (leaves[i].status == 1 ? "Approved" : "Rejected")) << "\n";
            any = true;
        }
        if (!any) {
            cout << "No leave requests.\n";
            return;
        }
        int id, decision;
        cout << "Enter request ID to process (0 to return): "; cin >> id;
        if (id == 0) return;
        cout << "1 Approve  2 Reject: "; cin >> decision;
        for (int i = 0; i < leaveCount; i++) {
            if (leaves[i].id == id && leaves[i].status == 0) {
                leaves[i].status = decision == 1 ? 1 : 2;
                cout << "Leave request processed.\n";
                return;
            }
        }
        cout << "Pending request not found.\n";
    }

    void addNotice() {
        if (noticeCount >= MAX_NOTICES) {
            cout << "Notice board is full.\n";
            return;
        }
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        cout << "Enter notice: ";
        getline(cin, notices[noticeCount++].message);
        cout << "Notice published.\n";
    }

    void showNotices() {
        cout << "\nHOSTEL NOTICE BOARD\n";
        if (noticeCount == 0) cout << "No notices available.\n";
        for (int i = 0; i < noticeCount; i++)
            cout << i + 1 << ". " << notices[i].message << "\n";
    }

    void updateGPA() {
        int id; double gpa;
        cout << "Student ID: "; cin >> id;
        int si = findStudentIndex(id);
        if (si == -1) {
            cout << "Student not found.\n";
            return;
        }
        cout << "New GPA: "; cin >> gpa;
        if (gpa < 0 || gpa > 4) {
            cout << "GPA must be between 0 and 4.\n";
            return;
        }
        students[si].gpa = gpa;
        cout << "GPA updated. New floor entitlement: "
             << entitledFloor(students[si]) << "\n";
        cout << "Any room change is subject to availability and warden approval.\n";
    }

    void checkoutStudent() {
        int id; cout << "Student ID: "; cin >> id;
        int si = findStudentIndex(id);
        if (si == -1) {
            cout << "Active student not found.\n";
            return;
        }
        Student &s = students[si];
        int refund = (int)s.deposit - calculateFine(s.lateCount);
        if (refund < 0) refund = 0;
        cout << "Deposit: Rs. " << s.deposit << "\n"
             << "Late fines deducted: Rs. " << calculateFine(s.lateCount)
             << "\nRefund due: Rs. " << refund << "\n";
        if (s.roomIndex >= 0) clearRoomBed(s.roomIndex, s.bed);
        for (int i = 0; i < bookingCount; i++)
            if (bookings[i].studentId == id) bookings[i].active = false;
        s.active = false; s.roomIndex = -1; s.bed = -1;
        s.deposit = 0; s.bookingId = -1;
        removeWaitlistStudent(id);
        cout << "Checkout completed and bed released.\n";
    }

    // Recursive report calculation over the real student records.
    int countActiveStudentsRecursive(int index) {
        if (index >= studentCount) return 0;
        return (students[index].active ? 1 : 0) + countActiveStudentsRecursive(index + 1);
    }

    // Traverses arrays and linked lists to calculate dashboard totals.
    void showDashboard() {
        int active = countActiveStudentsRecursive(0);
        int outside = 0, due = 0, repeat = 0;
        int open = 0;
        for (int i = 0; i < studentCount; i++) {
            if (students[i].active) {
                if (students[i].outside) outside++;
                if (students[i].balance > 0) due++;
                if (students[i].lateCount >= 3) repeat++;
            }
        }
        ComplaintNode *cur = complaintHead;
        while (cur != NULL) {
            if (cur->data.status != 2) open++;
            cur = cur->next;
        }
        cout << "\n========== WARDEN DASHBOARD ==========\n";
        cout << "Active students: " << active << "\n";
        cout << "Total rooms: " << roomCount << "\n";
        for (int f = 1; f <= 3; f++) {
            int total = 0, occupied = 0;
            for (int i = 0; i < roomCount; i++)
                if (rooms[i].floor == f) {
                    total += rooms[i].capacity;
                    occupied += rooms[i].occupied;
                }
            cout << "Floor " << f << " occupancy: " << occupied << "/" << total << " beds\n";
        }
        cout << "Waitlist count: ";
        int wc = 0; WaitNode *w = waitHead;
        while (w != NULL) { wc++; w = w->next; }
        cout << wc << "\n";
        cout << "Students with pending fees: " << due << "\n";
        cout << "Open complaints: " << open << "\n";
        cout << "Students currently outside: " << outside << "\n";
        cout << "Repeat late offenders (3+): " << repeat << "\n";
        cout << "======================================\n";
    }

    void viewGateLogs() {
        if (gateCount == 0) {
            cout << "No gate records.\n";
            return;
        }
        for (int i = 0; i < gateCount; i++) {
            cout << "Student " << gateLogs[i].studentId << "  "
                 << (gateLogs[i].type == 1 ? "Sign-in" : "Sign-out")
                 << "  " << dateTimeText(gateLogs[i].timestamp)
                 << (gateLogs[i].late ? "  LATE VIOLATION" : "")
                 << (gateLogs[i].emergency ? "  EMERGENCY" : "") << "\n";
        }
    }

    void viewVisitors() {
        if (visitorCount == 0) {
            cout << "No visitor records.\n";
            return;
        }
        for (int i = 0; i < visitorCount; i++) {
            cout << i + 1 << ". " << visitors[i].name
                 << "  ID: " << visitors[i].identity
                 << "  Host: " << visitors[i].studentId
                 << "  In: " << dateTimeText(visitors[i].inTime)
                 << "  Out: " << (visitors[i].active ? "Still inside" : dateTimeText(visitors[i].outTime))
                 << (visitors[i].active ? "  INSIDE" : "  EXITED") << "\n";
        }
    }

    void line() {
        cout << "======================================================================\n";
    }

    void title(const string &heading) {
        cout << "\n";
        line();
        cout << "                    HOSTEL MANAGEMENT SYSTEM\n";
        cout << "                         " << heading << "\n";
        cout << "Current date/time: " << dateTimeText(currentTimestamp()) << "\n";
        line();
        processDeadlines();
    }

    void section(const string &heading) {
        cout << "\n--- " << heading << " ---\n";
    }

    void studentManagementMenu() {
        int choice;
        do {
            title("WARDEN / STUDENT MANAGEMENT");
            cout << "1. Register New Student\n";
            cout << "2. View All Students\n";
            cout << "3. Search Student Record\n";
            cout << "4. Update Student GPA\n";
            cout << "5. Checkout Student\n";
            cout << "0. Back to Warden Dashboard\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: addStudent(); break;
                case 2: listStudents(); break;
                case 3: searchStudent(); break;
                case 4: updateGPA(); break;
                case 5: checkoutStudent(); break;
                case 0: break;
                default: cout << "Invalid option. Please select 0-5.\n";
            }
        } while (choice != 0);
    }

    void accommodationMenu() {
        int choice;
        do {
            title("WARDEN / ROOM & ACCOMMODATION");
            cout << "1. View Complete Room Map\n";
            cout << "2. Allocate Room to Student\n";
            cout << "3. Confirm Student Deposit\n";
            cout << "4. View / Process Room Waitlist\n";
            cout << "5. View Room Availability Summary\n";
            cout << "0. Back to Warden Dashboard\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: displayRoomMap(); break;
                case 2: allocateRoom(); break;
                case 3: confirmDeposit(); break;
                case 4: processWaitlist(); break;
                case 5: showDashboard(); break;
                case 0: break;
                default: cout << "Invalid option. Please select 0-5.\n";
            }
        } while (choice != 0);
    }

    void financeMenu() {
        int choice;
        do {
            title("WARDEN / FINANCE & PAYMENTS");
            cout << "1. View Student Bill / Receipt\n";
            cout << "2. Record a Payment\n";
            cout << "3. View Fee Defaulters\n";
            cout << "0. Back to Warden Dashboard\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: generateReceipt(); break;
                case 2: recordPayment(); break;
                case 3: defaultersList(); break;
                case 0: break;
                default: cout << "Invalid option. Please select 0-3.\n";
            }
        } while (choice != 0);
    }

    void requestsMenu() {
        int choice;
        do {
            title("WARDEN / COMPLAINTS & REQUESTS");
            cout << "1. View All Complaints\n";
            cout << "2. Update Complaint Status\n";
            cout << "3. Review Leave Requests\n";
            cout << "4. Publish Hostel Notice\n";
            cout << "0. Back to Warden Dashboard\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: viewComplaints(); break;
                case 2: resolveComplaint(); break;
                case 3: manageLeaves(); break;
                case 4: addNotice(); break;
                case 0: break;
                default: cout << "Invalid option. Please select 0-4.\n";
            }
        } while (choice != 0);
    }

    void operationsMenu() {
        int choice;
        do {
            title("WARDEN / HOSTEL OPERATIONS");
            cout << "1. View Hostel Dashboard\n";
            cout << "0. Back to Warden Dashboard\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: showDashboard(); break;
                case 0: break;
                default: cout << "Invalid option. Please select 0-1.\n";
            }
        } while (choice != 0);
    }

    void reportsMenu() {
        int choice;
        do {
            title("WARDEN / REPORTS & SECURITY");
            cout << "1. View Gate Entry / Exit Logs\n";
            cout << "2. View Visitor Register\n";
            cout << "3. View Students Outside at Curfew\n";
            cout << "0. Back to Warden Dashboard\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: viewGateLogs(); break;
                case 2: viewVisitors(); break;
                case 3: outsideAtCurfew(); break;
                case 0: break;
                default: cout << "Invalid option. Please select 0-3.\n";
            }
        } while (choice != 0);
    }

    void studentMenu(int si) {
        int choice;
        do {
            title("STUDENT PORTAL");
            cout << "Logged in as: " << students[si].name << "  |  ID: " << students[si].id << "\n";
            section("MY ACCOUNT");
            cout << "1. View My Profile\n2. View My Bill\n";
            section("ACCOMMODATION");
            cout << "3. View Room Map\n4. Request / Book a Room\n";
            section("HELP & COMMUNICATION");
            cout << "5. File a Complaint\n6. Track My Complaints\n7. Submit Leave Request\n8. View Hostel Notices\n";
            section("SESSION");
            cout << "0. Logout / Back to Role Selection\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: showStudent(students[si]); break;
                case 2: showBill(si); break;
                case 3: displayRoomMap(); break;
                case 4: allocateRoom(si); break;
                case 5: fileComplaint(si); break;
                case 6: trackComplaint(students[si].id); break;
                case 7: requestLeave(si); break;
                case 8: showNotices(); break;
                case 0: cout << "You have been logged out.\n"; break;
                default: cout << "Invalid option. Please select 0-8.\n";
            }
        } while (choice != 0);
    }

    void wardenMenu() {
        int choice;
        do {
            title("WARDEN ADMINISTRATOR DASHBOARD");
            cout << "Administrative access granted.\n";
            cout << "\n  1. Student Management\n";
            cout << "  2. Room & Accommodation\n";
            cout << "  3. Finance & Payments\n";
            cout << "  4. Complaints & Requests\n";
            cout << "  5. Hostel Operations\n";
            cout << "  6. Reports & Security\n";
            cout << "\n  0. Logout / Back to Role Selection\n";
            cout << "\nSelect a section: ";
            cin >> choice;
            switch (choice) {
                case 1: studentManagementMenu(); break;
                case 2: accommodationMenu(); break;
                case 3: financeMenu(); break;
                case 4: requestsMenu(); break;
                case 5: operationsMenu(); break;
                case 6: reportsMenu(); break;
                case 0: cout << "Warden session ended.\n"; break;
                default: cout << "Invalid section. Please select 0-6.\n";
            }
        } while (choice != 0);
    }

    void guardMenu() {
        int choice;
        do {
            title("SECURITY / GUARD PORTAL");
            cout << "1. Student Gate Entry / Exit\n";
            cout << "2. Register Visitor Entry\n";
            cout << "3. Record Visitor Exit\n";
            cout << "4. View Visitor Register\n";
            cout << "5. View Gate Activity Logs\n";
            cout << "6. Curfew Monitoring\n";
            cout << "0. Logout / Back to Role Selection\n";
            cout << "\nSelect an option: ";
            cin >> choice;
            switch (choice) {
                case 1: gateAction(); break;
                case 2: visitorEntry(); break;
                case 3: visitorExit(); break;
                case 4: viewVisitors(); break;
                case 5: viewGateLogs(); break;
                case 6: outsideAtCurfew(); break;
                case 0: cout << "Guard session ended.\n"; break;
                default: cout << "Invalid option. Please select 0-6.\n";
            }
        } while (choice != 0);
    }

    bool login() {
        int role, pin, attempts = 0, id;
        title("WELCOME / ROLE SELECTION");
        cout << "Please choose your portal:\n\n";
        cout << "1. Warden / Administrator\n";
        cout << "2. Student Portal\n";
        cout << "3. Security / Guard Portal\n";
        cout << "0. Exit Application\n";
        cout << "\nSelect a role: ";
        cin >> role;
        if (role == 0) return false;
        if (role == 1 || role == 3) {
            while (attempts < 3) {
                pin = readPIN();
                if ((role == 1 && pin == wardenPin) ||
                    (role == 3 && pin == guardPin)) {
                    if (role == 1) wardenMenu();
                    else guardMenu();
                    return true;
                }
                attempts++;
                cout << "Incorrect PIN. Attempts remaining: " << 3 - attempts << "\n";
            }
            cout << "Login locked after three incorrect attempts.\n";
            return true;
        }
        if (role == 2) {
            cout << "Enter student ID: "; cin >> id;
            int si = findStudentIndex(id);
            if (si == -1) {
                cout << "Student record not found or inactive.\n";
                return true;
            }
            if (students[si].suspended) {
                cout << "Account suspended. Contact the warden.\n";
                return true;
            }
            cout << "Welcome, " << students[si].name << ".\n";
            showNotices();
            studentMenu(si);
            return true;
        }
        cout << "Invalid role.\n";
        return true;
    }

public:
    HostelSystem() {
        studentCount = bookingCount = gateCount = visitorCount = 0;
        leaveCount = noticeCount = 0;
        complaintCount = 0;
        nextBookingId = 1001;
        nextComplaintId = 5001;
        nextLeaveId = 7001;
        wardenPin = 1234;
        guardPin = 4321;
        waitHead = waitTail = NULL;
        complaintHead = NULL;
        initializeRooms();
        initializeSampleStudents();
    }

    ~HostelSystem() {
        while (waitHead != NULL) {
            WaitNode *temp = waitHead;
            waitHead = waitHead->next;
            delete temp;
        }
        while (complaintHead != NULL) {
            ComplaintNode *temp = complaintHead;
            complaintHead = complaintHead->next;
            delete temp;
        }
    }

    void run() {
        title("HOSTEL ADMINISTRATION PORTAL");
        cout << "Welcome to the Hostel Management System.\n";
        cout << "Warden PIN: 1234  |  Guard PIN: 4321\n";
        cout << "Sample student accounts are available for demonstration.\n";
        bool running = true;
        while (running) {
            running = login();
        }
        cout << "Thank you for using the Hostel Management System.\n";
    }
};

int main() {
    HostelSystem system;
    system.run();
    return 0;
}
