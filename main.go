package main

import (
	"bytes"
	"context"
	"crypto/md5"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"image"
	"image/color"
	"image/png"
	"io"
	"io/ioutil"
	"log"
	"math/rand"
	"mime/multipart"
	"net/http"
	"net/textproto"
	"net/url"
	"os"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/PuerkitoBio/goquery"
	"github.com/isucon/isucandar"
	"github.com/isucon/isucandar/agent"
	"github.com/isucon/isucandar/failure"
	"github.com/isucon/isucandar/score"
	"github.com/isucon/isucandar/worker"
)

// option.go
type Option struct {
	TargetHost               string
	RequestTimeout           time.Duration
	InitializeRequestTimeout time.Duration
	ExitErrorOnFail          bool
}

func (o Option) String() string {
	args := []string{
		"benchmarker",
		fmt.Sprintf("--target-host=%s", o.TargetHost),
		fmt.Sprintf("--request-timeout=%s", o.RequestTimeout),
		fmt.Sprintf("--initialize-request-timeout=%s", o.InitializeRequestTimeout),
		fmt.Sprintf("--exit-error-on-fail=%v", o.ExitErrorOnFail),
	}
	return strings.Join(args, " ")
}

func (o Option) NewAgent(forInitialize bool) (*agent.Agent, error) {
	agentOptions := []agent.AgentOption{
		agent.WithBaseURL(fmt.Sprintf("http://%s/", o.TargetHost)),
		agent.WithCloneTransport(agent.DefaultTransport),
	}
	if forInitialize {
		agentOptions = append(agentOptions, agent.WithTimeout(o.InitializeRequestTimeout))
	} else {
		agentOptions = append(agentOptions, agent.WithTimeout(o.RequestTimeout))
	}
	return agent.NewAgent(agentOptions...)
}

// model.go
type User struct {
	mu sync.RWMutex

	ID          int       `json:"id"`
	AccountName string    `json:"account_name"`
	Password    string    `json:"passhash"`
	Authority   int       `json:"authority"`
	DeleteFlag  int       `json:"del_flg"`
	CreatedAt   time.Time `json:"created_at"`

	csrfToken string
	Agent     *agent.Agent
}

type Post struct {
	ID        int       `json:"id"`
	UserID    int       `json:"user_id"`
	Imgdata   []byte    `json:"imgdata"`
	Body      string    `json:"body"`
	Mime      string    `json:"mime"`
	CreatedAt time.Time `json:"created_at"`
}

type Comment struct {
	ID        int       `json:"id"`
	PostID    int       `json:"post_id"`
	UserID    int       `json:"user_id"`
	Comment   string    `json:"comment"`
	CreatedAt time.Time `json:"created_at"`
}

// GetID()
func (m *User) GetID() int {
	if m == nil {
		return 0
	}
	return m.ID
}
func (m *Post) GetID() int {
	if m == nil {
		return 0
	}
	return m.ID
}
func (m *Comment) GetID() int {
	if m == nil {
		return 0
	}
	return m.ID
}

// GetCreatedAt()
func (m *User) GetCreatedAt() time.Time {
	if m == nil {
		return time.Unix(0, 0)
	}
	return m.CreatedAt
}
func (m *Post) GetCreatedAt() time.Time {
	if m == nil {
		return time.Unix(0, 0)
	}
	return m.CreatedAt
}
func (m *Comment) GetCreatedAt() time.Time {
	if m == nil {
		return time.Unix(0, 0)
	}
	return m.CreatedAt
}

// GetAgent
func (m *User) GetAgent(o Option) (*agent.Agent, error) {
	m.mu.RLock()
	a := m.Agent
	m.mu.RUnlock()

	if a != nil {
		return a, nil
	}
	m.mu.Lock()
	defer m.mu.Unlock()

	a, err := o.NewAgent(false)
	if err != nil {
		return nil, err
	}
	m.Agent = a
	return a, nil
}

func (m *User) ClearAgent() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.Agent = nil
}

func (m *User) SetCSRFToken(token string) {
	m.mu.Lock()
	m.csrfToken = token
	m.mu.Unlock()
}

func (m *User) GetCSRFToken() string {
	m.mu.RLock()
	token := m.csrfToken
	m.mu.RUnlock()

	return token
}

// set.go
type Model interface {
	GetID() int
	GetCreatedAt() time.Time
}

type Set[T Model] struct {
	mu   sync.RWMutex
	list []T
	dict map[int]T
}

func (s *Set[T]) Len() int {
	s.mu.RLock()
	defer s.mu.RUnlock()

	return len(s.list)
}

func (s *Set[T]) At(index int) T {
	s.mu.RLock()
	defer s.mu.RUnlock()

	if s.list == nil {
		return *new(T)
	}
	return s.list[index]
}

func (s *Set[T]) Get(id int) (T, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	if s.dict == nil {
		return *new(T), false
	}
	model, ok := s.dict[id]
	return model, ok
}

func (s *Set[T]) Add(model T) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	id := model.GetID()
	if id == 0 {
		return false
	}

	if len(s.list) == 0 {
		s.list = []T{model}
	} else {
		pos := 0
		for i := 0; i < len(s.list)-1; i++ {
			m := s.list[i]
			pos = i
			if m.GetCreatedAt().Before(model.GetCreatedAt()) {
				break
			}
			if m.GetCreatedAt().Equal(model.GetCreatedAt()) {
				if m.GetID() > model.GetID() {
					break
				}
			}
		}
		s.list = append(s.list[:pos+1], s.list[pos:]...)
		s.list[pos] = model
	}
	if s.dict == nil {
		s.dict = make(map[int]T, 0)
	}
	s.dict[id] = model
	return true
}

type UserSet struct {
	Set[*User]
}

type PostSet struct {
	Set[*Post]
}

type CommentSet struct {
	Set[*Comment]
}

type SetForEachFunc[T Model] func(idx int, model T)

func (s *Set[T]) ForEach(f SetForEachFunc[T]) {
	s.mu.RLock()
	list := s.list[:]
	s.mu.RUnlock()

	for idx, model := range list {
		f(idx, model)
	}
}

// dump.go
func (s *Set[T]) LoadJSON(jsonFile string) error {
	file, err := os.Open(jsonFile)
	if err != nil {
		return err
	}
	defer file.Close()

	models := []T{}

	decoder := json.NewDecoder(file)
	if err := decoder.Decode(&models); err != nil {
		return err
	}
	for _, model := range models {
		if !s.Add(model) {
			return fmt.Errorf("Unexpected error on dump loading: %v", model)
		}
	}
	return nil
}

// action.go

func GetInitializeAction(ctx context.Context, ag *agent.Agent) (*http.Response, error) {
	req, err := ag.GET("/initialize")
	if err != nil {
		return nil, err
	}
	return ag.Do(ctx, req)
}

func GetLoginAction(ctx context.Context, ag *agent.Agent) (*http.Response, error) {
	req, err := ag.GET("/login")
	if err != nil {
		return nil, err
	}
	return ag.Do(ctx, req)
}

func PostLoginAction(ctx context.Context, ag *agent.Agent, accountName, password string) (*http.Response, error) {
	values := url.Values{}
	values.Add("account_name", accountName)
	values.Add("password", password)

	req, err := ag.POST("/login", strings.NewReader(values.Encode()))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	return ag.Do(ctx, req)
}

func GetRootAction(ctx context.Context, ag *agent.Agent) (*http.Response, error) {
	req, err := ag.GET("/")
	if err != nil {
		return nil, err
	}
	return ag.Do(ctx, req)
}

func PostRootAction(ctx context.Context, ag *agent.Agent, post *Post, csrfToken string) (*http.Response, error) {
	img, err := randomImage()
	if err != nil {
		return nil, err
	}

	body := bytes.NewBuffer([]byte{})
	form := multipart.NewWriter(body)

	form.WriteField("body", post.Body)
	form.WriteField("csrf_token", csrfToken)

	fileHeader := make(textproto.MIMEHeader)
	fileHeader.Set(
		"Content-Disposition",
		fmt.Sprintf(
			`form-data; name="%s"; filename="%s"`,
			"file", "image.png",
		),
	)
	fileHeader.Set("Content-Type", "image/png")
	file, err := form.CreatePart(fileHeader)
	if err != nil {
		return nil, err
	}
	if _, err := file.Write(img); err != nil {
		return nil, err
	}

	form.Close()

	req, err := ag.POST("/", body)
	if err != nil {
		return nil, err
	}
	req.Header.Add("Content-Type", form.FormDataContentType())

	return ag.Do(ctx, req)
}

// validation.go
const (
	ErrInvalidStatusCode failure.StringCode = "status-code"
	ErrInvalidPath       failure.StringCode = "path"
	ErrNotFound          failure.StringCode = "not-found"
	ErrCSRFToken         failure.StringCode = "csrf-token"
	ErrInvalidPostOrder  failure.StringCode = "post-order"
	ErrInvalidAsset      failure.StringCode = "asset"
)

type ValidationError struct {
	Errors []error
}

func (v ValidationError) Error() string {
	messages := []string{}

	for _, err := range v.Errors {
		if err != nil {
			messages = append(messages, fmt.Sprintf("%v", err))
		}
	}
	return strings.Join(messages, "\n")
}

func (v ValidationError) IsEmpty() bool {
	for _, err := range v.Errors {
		if err != nil {
			if ve, ok := err.(ValidationError); ok {
				if !ve.IsEmpty() {
					return false
				}
			} else {
				return false
			}
		}
	}
	return true
}

func (v ValidationError) Add(step *isucandar.BenchmarkStep) {
	for _, err := range v.Errors {
		if err != nil {
			if ve, ok := err.(ValidationError); ok {
				ve.Add(step)
			} else {
				step.AddError(err)
			}
		}
	}
}

type ResponseValidator func(*http.Response) error

func ValidateResponse(res *http.Response, validators ...ResponseValidator) ValidationError {
	errs := []error{}

	for _, validator := range validators {
		if err := validator(res); err != nil {
			errs = append(errs, err)
		}
	}
	return ValidationError{
		Errors: errs,
	}
}

func WithStatusCode(statusCode int) ResponseValidator {
	return func(r *http.Response) error {
		if r.StatusCode != statusCode {
			return failure.NewError(
				ErrInvalidStatusCode,
				fmt.Errorf(
					"%s %s : expected(%d) != actual(%d)",
					r.Request.Method,
					r.Request.URL.Path,
					statusCode,
					r.StatusCode,
				),
			)
		}
		return nil
	}
}

func WithLocation(val string) ResponseValidator {
	return func(r *http.Response) error {
		target := r.Request.URL.ResolveReference(&url.URL{Path: val})
		if r.Header.Get("Location") != target.String() {
			return failure.NewError(
				ErrInvalidPath,
				fmt.Errorf(
					"%s %s : %s, expected(%s) != actual(%s)",
					r.Request.Method,
					r.Request.URL.Path,
					"Location",
					val,
					r.Header.Get("Location"),
				),
			)
		}
		return nil
	}
}

func WithIncludeBody(val string) ResponseValidator {
	return func(r *http.Response) error {
		defer r.Body.Close()
		body, err := ioutil.ReadAll(r.Body)
		if err != nil {
			return failure.NewError(
				ErrInvalidResponse,
				fmt.Errorf(
					"%s %s : %s",
					r.Request.Method,
					r.Request.URL.Path,
					err.Error(),
				),
			)
		}

		if bytes.IndexAny(body, val) == -1 {
			return failure.NewError(
				ErrNotFound,
				fmt.Errorf(
					"%s %s : %s is not found in body",
					r.Request.Method,
					r.Request.URL.Path,
					val,
				),
			)
		}
		return nil
	}
}

func WithCSRFToken(user *User) ResponseValidator {
	return func(r *http.Response) error {
		defer r.Body.Close()
		user.SetCSRFToken("")
		doc, err := goquery.NewDocumentFromReader(r.Body)
		if err != nil {
			return failure.NewError(
				ErrInvalidResponse,
				fmt.Errorf(
					"%s %s : %s",
					r.Request.Method,
					r.Request.URL.Path,
					err.Error(),
				),
			)
		}

		node := doc.Find(`input[name="csrf_token"]`).Get(0)
		if node == nil {
			return failure.NewError(
				ErrCSRFToken,
				fmt.Errorf(
					"%s %s : CSRF token is not found",
					r.Request.Method,
					r.Request.URL.Path,
				),
			)
		}

		for _, attr := range node.Attr {
			if attr.Key == "value" {
				user.SetCSRFToken(attr.Val)
			}
		}

		if user.GetCSRFToken() == "" {
			return failure.NewError(
				ErrCSRFToken,
				fmt.Errorf(
					"%s %s : CSRF token is not found",
					r.Request.Method,
					r.Request.URL.Path,
				),
			)
		}

		return nil
	}
}

func WithOrderedPosts() ResponseValidator {
	return func(r *http.Response) error {
		defer r.Body.Close()
		doc, err := goquery.NewDocumentFromReader(r.Body)

		if err != nil {
			return failure.NewError(
				ErrInvalidResponse,
				fmt.Errorf(
					"%s %s : %s",
					r.Request.Method,
					r.Request.URL.Path,
					err.Error(),
				),
			)
		}

		errs := []error{}
		previousCreatedAt := time.Now()
		doc.Find(".isu-posts .isu-post").Each(func(_ int, s *goquery.Selection) {
			post := s.First()
			idAttr, exists := post.Attr("id")
			if !exists {
				return
			}
			createdAtAttr, exists := post.Attr("data-created-at")
			if !exists {
				return
			}

			id, _ := strconv.Atoi(strings.TrimPrefix(idAttr, "pid_"))
			createdAt, _ := time.Parse(time.RFC3339, createdAtAttr)

			if createdAt.After(previousCreatedAt) {
				errs = append(errs,
					failure.NewError(
						ErrInvalidPostOrder,
						fmt.Errorf(
							"%s %s : invalid order in top page: %s",
							r.Request.Method,
							r.Request.URL.Path,
							createdAt,
						),
					),
				)
				AdminLogger.Printf("isu-post: %d: %s", id, createdAt)
			}
			// Maybe this is missing in original implementation
			previousCreatedAt = createdAt
		})

		// したと揃えてもいいかも
		return ValidationError{
			Errors: errs,
		}
	}
}

var (
	assetsMD5 = map[string]string{
		"favicon.ico":       "ad4b0f606e0f8465bc4c4c170b37e1a3",
		"js/timeago.min.js": "f2d4c53400d0a46de704f5a97d6d04fb",
		"js/main.js":        "9c309fed7e360c57a705978dab2c68ad",
		"css/style.css":     "e4c3606a18d11863189405eb5c6ca551",
	}
)

func WithAssets(ctx context.Context, ag *agent.Agent) ResponseValidator {
	return func(r *http.Response) error {
		resources, err := ag.ProcessHTML(ctx, r, r.Body)
		if err != nil {
			return failure.NewError(
				ErrInvalidAsset,
				fmt.Errorf(
					"%s %s : %s",
					r.Request.Method,
					r.Request.URL.Path,
					err.Error(),
				),
			)
		}

		errs := []error{}

		for uri, res := range resources {
			path := strings.TrimPrefix(uri, ag.BaseURL.String())
			if res.Error != nil {
				errs = append(errs, failure.NewError(
					ErrInvalidAsset,
					fmt.Errorf(
						"%s /%s : %s",
						"GET",
						path,
						res.Error,
					),
				),
				)
				continue
			}
			defer res.Response.Body.Close()

			if res.Response.StatusCode == 304 {
				continue
			}

			expectedMD5, ok := assetsMD5[path]
			if !ok {
				continue
			}

			hash := md5.New()
			io.Copy(hash, res.Response.Body)
			actualMD5 := hex.EncodeToString(hash.Sum(nil))
			if expectedMD5 != actualMD5 {
				errs = append(errs, failure.NewError(
					ErrInvalidAsset,
					fmt.Errorf(
						"%s /%s : expected(MD5 %s) != actual(MD5 %s)",
						"GET",
						path,
						expectedMD5,
						actualMD5,
					),
				),
				)
			}
		}

		return ValidationError{
			Errors: errs,
		}
	}
}

// scenario.go
const (
	ErrFailedLoadJSON  failure.StringCode = "load-json"
	ErrCannotNewAgent  failure.StringCode = "agent"
	ErrInvalidRequest  failure.StringCode = "request"
	ErrInvalidResponse failure.StringCode = "response"
)

const (
	ScoreGETLogin  score.ScoreTag = "GET /login"
	ScorePOSTLogin score.ScoreTag = "POST /login"
	ScoreGETRoot   score.ScoreTag = "GET /"
	ScorePOSTRoot  score.ScoreTag = "POST /"
)

type Scenario struct {
	Option   Option
	Users    UserSet
	Posts    PostSet
	Comments CommentSet
}

func (s *Scenario) Prepare(ctx context.Context, step *isucandar.BenchmarkStep) error {
	if err := s.Users.LoadJSON("./dump/users.json"); err != nil {
		return failure.NewError(ErrFailedLoadJSON, err)
	}
	if err := s.Posts.LoadJSON("./dump/posts.json"); err != nil {
		return failure.NewError(ErrFailedLoadJSON, err)
	}
	if err := s.Comments.LoadJSON("./dump/comments.json"); err != nil {
		return failure.NewError(ErrFailedLoadJSON, err)
	}

	ag, err := s.Option.NewAgent(true)
	if err != nil {
		return failure.NewError(ErrCannotNewAgent, err)
	}

	res, err := GetInitializeAction(ctx, ag)
	if err != nil {
		return failure.NewError(ErrInvalidRequest, err)
	}
	defer res.Body.Close()

	ValidateResponse(
		res,
		WithStatusCode(200),
	).Add(step)

	return nil
}

func (s *Scenario) Load(ctx context.Context, step *isucandar.BenchmarkStep) error {
	wg := &sync.WaitGroup{}

	successCase, err := worker.NewWorker(func(ctx context.Context, _ int) {
		if user, ok := s.Users.Get(rand.Intn(s.Users.Len())); ok {
			if user.DeleteFlag != 0 {
				return
			}

			if s.LoginSuccess(ctx, step, user) {
				s.PostImage(ctx, step, user)
			}
			user.ClearAgent()
		}
	},
		worker.WithInfinityLoop(),
		worker.WithMaxParallelism(4))
	if err != nil {
		return err
	}

	wg.Add(1)
	go func() {
		defer wg.Done()
		successCase.Process(ctx)
	}()

	failureCase, err := worker.NewWorker(func(ctx context.Context, _ int) {
		if user, ok := s.Users.Get(rand.Intn(s.Users.Len())); ok {
			if user.DeleteFlag != 0 {
				return
			}
			s.LoginFailure(ctx, step, user)
		}
	},
		worker.WithLoopCount(20),
		worker.WithMaxParallelism(2))
	if err != nil {
		return err
	}

	wg.Add(1)
	go func() {
		defer wg.Done()
		failureCase.Process(ctx)
	}()

	orderedCase, err := worker.NewWorker(func(ctx context.Context, _ int) {
		if user, ok := s.Users.Get(rand.Intn(s.Users.Len())); ok {
			s.OrderedIndex(ctx, step, user)
		}
	},
		worker.WithInfinityLoop(),
		worker.WithMaxParallelism(2))
	if err != nil {
		return err
	}

	wg.Add(1)
	go func() {
		defer wg.Done()
		orderedCase.Process(ctx)
	}()

	wg.Wait()
	return nil
}

func (s *Scenario) Validation(ctx context.Context, step *isucandar.BenchmarkStep) error {
	return nil
}

func (s *Scenario) LoginSuccess(ctx context.Context, step *isucandar.BenchmarkStep, user *User) bool {
	ag, err := user.GetAgent(s.Option)
	if err != nil {
		step.AddError(failure.NewError(ErrCannotNewAgent, err))
		return false
	}

	getRes, err := GetLoginAction(ctx, ag)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer getRes.Body.Close()

	getValidation := ValidateResponse(
		getRes,
		WithStatusCode(200),
		WithAssets(ctx, ag),
	)
	getValidation.Add(step)

	if getValidation.IsEmpty() {
		step.AddScore(ScoreGETLogin)
	} else {
		return false
	}

	select {
	case <-ctx.Done():
		return false
	default:
	}

	postRes, err := PostLoginAction(ctx, ag, user.AccountName, user.Password)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer postRes.Body.Close()

	postValidation := ValidateResponse(
		postRes,
		WithStatusCode(302),
		WithLocation("/"),
	)
	postValidation.Add(step)

	if postValidation.IsEmpty() {
		step.AddScore(ScorePOSTLogin)
	} else {
		return false
	}
	return true
}

func (s *Scenario) LoginFailure(ctx context.Context, step *isucandar.BenchmarkStep, user *User) bool {
	ag, err := user.GetAgent(s.Option)
	if err != nil {
		step.AddError(failure.NewError(ErrCannotNewAgent, err))
		return false
	}

	getRes, err := GetLoginAction(ctx, ag)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer getRes.Body.Close()

	getValidation := ValidateResponse(
		getRes,
		WithStatusCode(200),
		WithAssets(ctx, ag),
	)
	getValidation.Add(step)

	if getValidation.IsEmpty() {
		step.AddScore(ScoreGETLogin)
	} else {
		return false
	}

	select {
	case <-ctx.Done():
		return false
	default:
	}
	postRes, err := PostLoginAction(ctx, ag, user.AccountName, user.Password+".invalid")
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer postRes.Body.Close()

	postValidation := ValidateResponse(
		postRes,
		WithStatusCode(302),
		WithLocation("/login"),
	)
	postValidation.Add(step)

	if postValidation.IsEmpty() {
		step.AddScore(ScorePOSTLogin)
	} else {
		return false
	}

	select {
	case <-ctx.Done():
		return false
	default:
	}

	redirectRes, err := GetLoginAction(ctx, ag)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	// ここも多分タイポしてる
	defer redirectRes.Body.Close()

	redirectValidation := ValidateResponse(
		redirectRes,
		WithStatusCode(200),
		WithIncludeBody("アカウント名かパスワードが間違っています"),
	)
	redirectValidation.Add(step)

	if redirectValidation.IsEmpty() {
		step.AddScore(ScoreGETLogin)
	} else {
		return false
	}

	return true
}

func (s *Scenario) PostImage(ctx context.Context, step *isucandar.BenchmarkStep, user *User) bool {
	ag, err := user.GetAgent(s.Option)
	if err != nil {
		step.AddError(failure.NewError(ErrCannotNewAgent, err))
		return false
	}

	getRes, err := GetRootAction(ctx, ag)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer getRes.Body.Close()

	getValidation := ValidateResponse(
		getRes,
		WithStatusCode(200),
		WithCSRFToken(user),
	)
	getValidation.Add(step)

	if getValidation.IsEmpty() {
		step.AddScore(ScoreGETRoot)
	} else {
		return false
	}

	select {
	case <-ctx.Done():
		return false
	default:
	}

	post := &Post{
		Mime:   "image/png",
		Body:   randomText(),
		UserID: user.ID,
	}
	postRes, err := PostRootAction(ctx, ag, post, user.GetCSRFToken())
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer postRes.Body.Close()

	postValidation := ValidateResponse(
		postRes,
		WithStatusCode(302),
	)
	postValidation.Add(step)

	if postValidation.IsEmpty() {
		step.AddScore(ScorePOSTRoot)
	} else {
		return false
	}

	select {
	case <-ctx.Done():
		return false
	default:
	}

	redirectRes, err := GetLoginAction(ctx, ag)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	// ここも多分タイポしてる
	defer redirectRes.Body.Close()

	redirectValidation := ValidateResponse(
		redirectRes,
		WithStatusCode(200),
		WithAssets(ctx, ag),
	)
	redirectValidation.Add(step)

	if redirectValidation.IsEmpty() {
		step.AddScore(ScoreGETRoot)
	} else {
		return false
	}

	return true
}

func (s *Scenario) OrderedIndex(ctx context.Context, step *isucandar.BenchmarkStep, user *User) bool {
	ag, err := user.GetAgent(s.Option)
	if err != nil {
		step.AddError(failure.NewError(ErrCannotNewAgent, err))
		return false
	}

	getRes, err := GetRootAction(ctx, ag)
	if err != nil {
		step.AddError(failure.NewError(ErrInvalidRequest, err))
		return false
	}
	defer getRes.Body.Close()

	getValidation := ValidateResponse(
		getRes,
		WithStatusCode(200),
		WithOrderedPosts(),
	)
	getValidation.Add(step)

	if getValidation.IsEmpty() {
		step.AddScore(ScoreGETRoot)
	} else {
		return false
	}

	return true
}

// random.go
func randomColor() color.RGBA {
	c := uint8(rand.Intn(255))
	return color.RGBA{c, c, c, 255}
}

func randomImage() ([]byte, error) {
	size := image.Rect(0, 0, 640, 480)
	img := image.NewRGBA(size)
	for x := 0; x < size.Dx(); x++ {
		for y := 0; y < size.Dy(); y++ {
			img.SetRGBA(x, y, randomColor())
		}
	}

	buf := bytes.NewBuffer([]byte{})
	if err := png.Encode(buf, img); err != nil {
		return nil, err
	}

	return buf.Bytes(), nil
}

var (
	randomStringPrefixes = []string{
		"Hello",
		"Hi",
		"Yay",
		"Oh",
		"Wow",
	}
	randomStringSuffixes = []string{
		"World",
		"Baby",
		"Image",
		"My Photo",
		"Great Picture",
	}
)

func randomText() string {
	prefix := randomStringPrefixes[rand.Intn(len(randomStringPrefixes))]
	suffix := randomStringSuffixes[rand.Intn(len(randomStringSuffixes))]

	return prefix + ", " + suffix
}

// main.go
var (
	ContestantLogger = log.New(os.Stdout, "", log.Ltime|log.Lmicroseconds)
	AdminLogger      = log.New(os.Stderr, "[ADMIN] ", log.Ltime|log.Lmicroseconds)
)

const (
	DefaultTargetHost               = "localhost:8080"
	DefaultRequestTimeout           = 3 * time.Second
	DefaultInitializeRequestTimeout = 10 * time.Second
	DefaultExitErrorOnFail          = true
)

func main() {
	option := Option{}

	flag.StringVar(&option.TargetHost, "target-host", DefaultTargetHost, "Benchmark target host with port")
	flag.DurationVar(&option.RequestTimeout, "request-timeout", DefaultRequestTimeout, "Default request timeout")
	flag.DurationVar(&option.InitializeRequestTimeout, "initialize-request-timeout", DefaultInitializeRequestTimeout, "Initialize request timeout")
	flag.BoolVar(&option.ExitErrorOnFail, "exit-error-on-fail", DefaultExitErrorOnFail, "Exit with error if benchmark fails")
	flag.Parse()
	AdminLogger.Print(option)

	scenario := &Scenario{
		Option: option,
	}
	benchmark, err := isucandar.NewBenchmark(
		isucandar.WithoutPanicRecover(),
		isucandar.WithLoadTimeout(1*time.Minute),
	)
	if err != nil {
		AdminLogger.Fatal(err)
	}
	benchmark.AddScenario(scenario)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	result := benchmark.Start(ctx)

	for _, err := range result.Errors.All() {
		// error msg
		ContestantLogger.Printf("%v", err)
		// error msg with stack trace
		AdminLogger.Printf("%+v", err)
	}

	for tag, count := range result.Score.Breakdown() {
		ContestantLogger.Printf("%s: %d", tag, count)
	}
	ContestantLogger.Printf("Error: %d", len(result.Errors.All()))

	score := SumScore(result)
	ContestantLogger.Printf("score: %d", score)
	if option.ExitErrorOnFail && score <= 0 {
		os.Exit(1)
	}
}

func SumScore(result *isucandar.BenchmarkResult) int64 {
	score := result.Score

	score.Set(ScoreGETRoot, 1)
	score.Set(ScoreGETLogin, 1)
	score.Set(ScorePOSTLogin, 1)
	score.Set(ScorePOSTRoot, 1)

	addition := score.Sum()
	deduction := len(result.Errors.All())

	sum := addition - int64(deduction)
	if sum < 0 {
		sum = 0
	}
	return sum
}
